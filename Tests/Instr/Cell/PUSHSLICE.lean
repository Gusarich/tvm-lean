import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Native
import TvmLean.Validation.Canon.Result
import TvmLean.Validation.Oracle.Report
import TvmLean.Validation.Oracle.Runner

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PUSHSLICE

/-
PUSHSLICE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/PushSliceConst.lean` (dispatch + push path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0x8b`, `0x8c`, `0x8d` decode families)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.pushSliceConst` rejected by generic assembler)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_push_slice_common`, `exec_push_slice`, `exec_push_slice_r`, `exec_push_slice_r2`)

Branch map covered by this suite:
- exec handler dispatch: `.pushSliceConst` vs fallthrough `next`;
- decode family split at opcode boundaries `0x8b` (12-bit), `0x8c` (15-bit), `0x8d` (18-bit);
- family-specific decode guards for payload-bit sufficiency and ref sufficiency;
- `0x8d` explicit invalid-refs gate (`refs > 4` => `invOpcode`);
- trailing-marker stripping (`bitsStripTrailingMarker`) for inline payloads.
-/

private def dispatchSentinel : Int := 839

private def pushSliceOpcode8 : Nat := 0x8b
private def pushSliceOpcode15 : Nat := 0x8c
private def pushSliceOpcode18 : Nat := 0x8d

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def fromExceptIO {α} (label : String) (res : Except String α) : IO α := do
  match res with
  | .ok v => pure v
  | .error e => failUnit s!"{label}: {e}"

private def pushSliceDataBits8 (len4 : Nat) : Nat :=
  len4 * 8 + 4

private def pushSliceDataBits15 (bits5 : Nat) : Nat :=
  bits5 * 8 + 1

private def pushSliceDataBits18 (len7 : Nat) : Nat :=
  len7 * 8 + 6

private def patternBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 0) || ((i.1 + phase) % 5 = 1)

private def runPushSliceDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushSliceConst instr stack

private def runPushSliceDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushSliceConst instr
    (VM.push (intV dispatchSentinel)) stack

private def expectDecodeInvOpcode (label : String) (s : Slice) : IO Unit := do
  match decodeCp0WithBits s with
  | .error .invOpcode => pure ()
  | .error e => failUnit s!"{label}: expected invOpcode, got {e}"
  | .ok (instr, bits, _) =>
      failUnit s!"{label}: expected invOpcode, got {reprStr instr} ({bits} bits)"

private def assembleCode (program : Array Instr) : Except String Cell := do
  if program.isEmpty then
    pure Cell.empty
  else
    match assembleCp0 program.toList with
    | .ok c => pure c
    | .error e => throw s!"assemble failed: {e}"

private def appendCodeCell (a b : Cell) : Except String Cell := do
  if a.bits.size + b.bits.size > 1023 then
    throw "code append overflow (bits > 1023)"
  if a.refs.size + b.refs.size > 4 then
    throw "code append overflow (refs > 4)"
  pure (Cell.mkOrdinary (a.bits ++ b.bits) (a.refs ++ b.refs))

private def mkCodeWithPreludeTail
    (prelude : Array Instr)
    (core : Cell)
    (tail : Array Instr := #[]) : Except String Cell := do
  let preCell ← assembleCode prelude
  let tailCell ← assembleCode tail
  let x ← appendCodeCell preCell core
  appendCodeCell x tailCell

private def encodeRawWithMarker (payload : BitString) (dataBits : Nat) : Except String BitString := do
  if payload.size + 1 > dataBits then
    throw s!"payload too large: payload={payload.size}, dataBits={dataBits}"
  pure (payload ++ #[true] ++ Array.replicate (dataBits - payload.size - 1) false)

private def mkPushSlice8CodeFromRaw (len4 : Nat) (raw : BitString) : Except String Cell := do
  if len4 > 15 then
    throw s!"len4 out of range: {len4}"
  let word12 : Nat := (pushSliceOpcode8 <<< 4) + len4
  pure (Cell.mkOrdinary (natToBits word12 12 ++ raw) #[])

private def mkPushSlice15CodeFromRaw
    (r2 : Nat)
    (bits5 : Nat)
    (raw : BitString)
    (refs : Array Cell) : Except String Cell := do
  if r2 > 3 then
    throw s!"r2 out of range: {r2}"
  if bits5 > 31 then
    throw s!"bits5 out of range: {bits5}"
  let word15 : Nat := (pushSliceOpcode15 <<< 7) + (r2 <<< 5) + bits5
  pure (Cell.mkOrdinary (natToBits word15 15 ++ raw) refs)

private def mkPushSlice18CodeFromRaw
    (refs3 : Nat)
    (len7 : Nat)
    (raw : BitString)
    (refs : Array Cell) : Except String Cell := do
  if refs3 > 7 then
    throw s!"refs3 out of range: {refs3}"
  if len7 > 127 then
    throw s!"len7 out of range: {len7}"
  let word18 : Nat := (pushSliceOpcode18 <<< 10) + (refs3 <<< 7) + len7
  pure (Cell.mkOrdinary (natToBits word18 18 ++ raw) refs)

private def mkPushSlice8InstrCode
    (payload : BitString)
    (len4 : Nat) : Except String (Instr × Cell) := do
  if len4 > 15 then
    throw s!"len4 out of range: {len4}"
  let dataBits := pushSliceDataBits8 len4
  let raw ← encodeRawWithMarker payload dataBits
  let code ← mkPushSlice8CodeFromRaw len4 raw
  let instr : Instr := .pushSliceConst (Slice.ofCell (Cell.mkOrdinary payload #[]))
  pure (instr, code)

private def mkPushSlice15InstrCode
    (payload : BitString)
    (r2 : Nat)
    (bits5 : Nat)
    (refs : Array Cell) : Except String (Instr × Cell) := do
  if r2 > 3 then
    throw s!"r2 out of range: {r2}"
  if refs.size != r2 + 1 then
    throw s!"refs size mismatch: expected {r2 + 1}, got {refs.size}"
  let dataBits := pushSliceDataBits15 bits5
  let raw ← encodeRawWithMarker payload dataBits
  let code ← mkPushSlice15CodeFromRaw r2 bits5 raw refs
  let instr : Instr := .pushSliceConst (Slice.ofCell (Cell.mkOrdinary payload refs))
  pure (instr, code)

private def mkPushSlice18InstrCode
    (payload : BitString)
    (refs3 : Nat)
    (len7 : Nat)
    (refs : Array Cell) : Except String (Instr × Cell) := do
  if refs3 > 4 then
    throw s!"refs3 out of PUSHSLICE range: {refs3}"
  if refs.size != refs3 then
    throw s!"refs size mismatch: expected {refs3}, got {refs.size}"
  let dataBits := pushSliceDataBits18 len7
  let raw ← encodeRawWithMarker payload dataBits
  let code ← mkPushSlice18CodeFromRaw refs3 len7 raw refs
  let instr : Instr := .pushSliceConst (Slice.ofCell (Cell.mkOrdinary payload refs))
  pure (instr, code)

private def mkTruncated8Code (len4 : Nat) : Except String Cell := do
  let raw ← encodeRawWithMarker #[true] (pushSliceDataBits8 len4)
  mkPushSlice8CodeFromRaw len4 (raw.take (raw.size - 1))

private def mkTruncated15Code (r2 : Nat) (bits5 : Nat) : Except String Cell := do
  if r2 > 3 then
    throw s!"r2 out of range: {r2}"
  let raw ← encodeRawWithMarker #[true] (pushSliceDataBits15 bits5)
  let refs := Array.replicate (r2 + 1) Cell.empty
  mkPushSlice15CodeFromRaw r2 bits5 (raw.take (raw.size - 1)) refs

private def mkTruncated18Code (refs3 : Nat) (len7 : Nat) : Except String Cell := do
  let raw ← encodeRawWithMarker #[true] (pushSliceDataBits18 len7)
  let refs := Array.replicate refs3 Cell.empty
  mkPushSlice18CodeFromRaw refs3 len7 (raw.take (raw.size - 1)) refs

private def mkMissingRefs15Code (r2 : Nat) (bits5 : Nat) : Except String Cell := do
  if r2 > 3 then
    throw s!"r2 out of range: {r2}"
  let raw ← encodeRawWithMarker #[] (pushSliceDataBits15 bits5)
  let refsNeeded : Nat := r2 + 1
  let refsProvided : Array Cell := Array.replicate (refsNeeded - 1) Cell.empty
  mkPushSlice15CodeFromRaw r2 bits5 raw refsProvided

private def mkMissingRefs18Code (refs3 : Nat) (len7 : Nat) : Except String Cell := do
  if refs3 = 0 then
    throw "refs3 must be >= 1 for missing-refs shape"
  let raw ← encodeRawWithMarker #[] (pushSliceDataBits18 len7)
  let refsProvided : Array Cell := Array.replicate (refs3 - 1) Cell.empty
  mkPushSlice18CodeFromRaw refs3 len7 raw refsProvided

private structure RawOracleCase where
  name : String
  code : Cell
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

private def mkRawCaseFromCode
    (name : String)
    (code : Cell)
    (initStack : Array Value := #[])
    (fuel : Nat := 1_000_000) : RawOracleCase :=
  { name, code, initStack, fuel }

private def mkRawCase8
    (name : String)
    (payload : BitString)
    (len4 : Nat)
    (initStack : Array Value := #[])
    (prelude : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase := do
  let (_, core) ← mkPushSlice8InstrCode payload len4
  let code ← mkCodeWithPreludeTail prelude core tail
  pure { name, code, initStack, fuel }

private def mkRawCase15
    (name : String)
    (payload : BitString)
    (r2 : Nat)
    (bits5 : Nat)
    (refs : Array Cell)
    (initStack : Array Value := #[])
    (prelude : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase := do
  let (_, core) ← mkPushSlice15InstrCode payload r2 bits5 refs
  let code ← mkCodeWithPreludeTail prelude core tail
  pure { name, code, initStack, fuel }

private def mkRawCase18
    (name : String)
    (payload : BitString)
    (refs3 : Nat)
    (len7 : Nat)
    (refs : Array Cell)
    (initStack : Array Value := #[])
    (prelude : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase := do
  let (_, core) ← mkPushSlice18InstrCode payload refs3 len7 refs
  let code ← mkCodeWithPreludeTail prelude core tail
  pure { name, code, initStack, fuel }

private def toBocHex (c : Cell) : Except String String := do
  let bytes ←
    match stdBocSerialize c with
    | .ok b => pure b
    | .error e => throw s!"stdBocSerialize failed: {e}"
  pure (TvmLeanOracleValidate.bytesToHex bytes)

private def valueToOracleToken (v : Value) : Except String String := do
  match v with
  | .int (.num n) => pure (toString n)
  | .int .nan => throw "cannot encode NaN in oracle stack token stream"
  | .null => pure "N"
  | .cell c =>
      let hex ← toBocHex c
      pure s!"CB:{hex}"
  | .slice s =>
      if s.bitPos = 0 && s.refPos = 0 && s.bitsRemaining = s.cell.bits.size && s.refsRemaining = s.cell.refs.size then
        let hex ← toBocHex s.cell
        pure s!"SB:{hex}"
      else
        throw "only full-cell slices are supported in oracle stack token stream"
  | .builder b =>
      if b.bits.isEmpty && b.refs.isEmpty then
        pure "B"
      else
        throw "non-empty builders are not yet supported in oracle stack token stream"
  | .tuple t =>
      if t.isEmpty then
        pure "T"
      else
        throw "non-empty tuples are not yet supported in oracle stack token stream"
  | .cont (.quit 0) => pure "K"
  | .cont _ => throw "only quit(0) continuations are supported in oracle stack token stream"

private def stackToOracleTokens (stack : Array Value) : Except String (List String) := do
  let mut out : List String := []
  for v in stack do
    let tok ← valueToOracleToken v
    out := out.concat tok
  pure out

private def leanCanonResult (res : StepResult) : Except String CanonResult := do
  match res with
  | .halt exitCode stF =>
      let (c4Out, c5Out) := TvmLeanOracleValidate.leanOutCells stF
      pure (CanonResult.ofLeanState (~~~ exitCode) stF.gas.gasConsumed c4Out c5Out stF.stack)
  | .continue _ =>
      throw "Lean execution did not halt within fuel"

private def runRawOracleBatchCompare (label : String) (cases : Array RawOracleCase) : IO Unit := do
  let mut batch : Array (Cell × List String) := #[]
  let mut names : Array String := #[]
  let mut leanCanons : Array CanonResult := #[]
  for c in cases do
    let stackTokens ←
      match stackToOracleTokens c.initStack with
      | .ok toks => pure toks
      | .error e => failUnit s!"{label}/{c.name}: {e}"
    let leanCanon ←
      match leanCanonResult (TvmLeanOracleValidate.runLean c.code c.initStack c.fuel) with
      | .ok canon => pure canon
      | .error e => failUnit s!"{label}/{c.name}: {e}"
    batch := batch.push (c.code, stackTokens)
    names := names.push c.name
    leanCanons := leanCanons.push leanCanon
  let oracleOuts ← TvmLeanOracleValidate.runOracleBatch batch
  if oracleOuts.size != cases.size then
    failUnit s!"{label}: oracle output size mismatch (expected={cases.size}, got={oracleOuts.size})"
  for i in [0:cases.size] do
    let out ←
      match oracleOuts[i]? with
      | some o => pure o
      | none => failUnit s!"{label}: internal oracle index out of bounds at {i}"
    let oracleCanon := CanonResult.ofOracleRaw out.exitRaw out.gasUsed out.c4Hash out.c5Hash out.stackTop
    let leanCanon ←
      match leanCanons[i]? with
      | some c => pure c
      | none => failUnit s!"{label}: internal lean-canon index out of bounds at {i}"
    let cmp := compareCanonResults leanCanon oracleCanon
    if !cmp.ok then
      let reason :=
        match cmp.mismatch? with
        | some m => m.message
        | none => "oracle comparison failed"
      let caseName :=
        match names[i]? with
        | some n => n
        | none => s!"case-{i}"
      failUnit s!"{label}/{caseName}: {reason}"

private def runCodeVm
    (code : Cell)
    (initStack : Array Value)
    (gasLimit : Int := 1_000_000)
    (gasMax : Int := 1_000_000)
    (fuel : Nat := 200_000) : StepResult :=
  let st0 := { (VmState.initial code gasLimit gasMax 0) with stack := initStack }
  VmState.run nativeHost fuel st0

private def expectExitCode (label : String) (expected : Int) (res : StepResult) : IO VmState := do
  match res with
  | .halt exitCode st =>
      if exitCode = expected then
        pure st
      else
        failUnit s!"{label}: expected exit={expected}, got {exitCode}"
  | .continue _ =>
      failUnit s!"{label}: execution did not halt"

private def handcraftedOracleCases : IO (Array RawOracleCase) := do
  let refA : Cell := Cell.empty
  let refB : Cell := Cell.ofUInt 1 1
  let refC : Cell := Cell.ofUInt 2 2
  let refD : Cell := Cell.ofUInt 3 5
  let refE : Cell := Cell.mkOrdinary (natToBits 0b101011 6) #[refB]
  let payload8bMax : BitString := patternBits 123 0
  let payload8cMax : BitString := patternBits 248 1
  let payload8dMax : BitString := patternBits 997 2
  let mut cases : Array RawOracleCase := #[]

  -- Success: 8b family.
  cases := cases.push (← fromExceptIO "oracle/01"
    (mkRawCase8 "oracle/ok/8b/empty" #[] 0))
  cases := cases.push (← fromExceptIO "oracle/02"
    (mkRawCase8 "oracle/ok/8b/bit1" #[true] 0))
  cases := cases.push (← fromExceptIO "oracle/03"
    (mkRawCase8 "oracle/ok/8b/trailing-zeros" #[true, false, false, true, false, false, false] 1))
  cases := cases.push (← fromExceptIO "oracle/04"
    (mkRawCase8 "oracle/ok/8b/max-len15-payload123" payload8bMax 15))
  cases := cases.push (← fromExceptIO "oracle/05"
    (mkRawCase8 "oracle/ok/8b/deep-stack-null" (natToBits 0b101 3) 0 #[.null]))
  cases := cases.push (← fromExceptIO "oracle/06"
    (mkRawCase8 "oracle/ok/8b/deep-stack-int-cell"
      (natToBits 0x2a 6) 1 #[intV (-7), .cell refC]))
  cases := cases.push (← fromExceptIO "oracle/07"
    (mkRawCase8 "oracle/ok/8b/prelude-and-tail" (natToBits 0x15 5) 1 #[] #[.pushNull] #[.nop]))

  -- Success: 8c family.
  cases := cases.push (← fromExceptIO "oracle/08"
    (mkRawCase15 "oracle/ok/8c/r0-bits0-ref1-empty" #[] 0 0 #[refA]))
  cases := cases.push (← fromExceptIO "oracle/09"
    (mkRawCase15 "oracle/ok/8c/r0-bits1-ref1" (natToBits 0b1011011 7) 0 1 #[refB]))
  cases := cases.push (← fromExceptIO "oracle/10"
    (mkRawCase15 "oracle/ok/8c/r1-bits5-ref2" (patternBits 39 1) 1 5 #[refA, refC]))
  cases := cases.push (← fromExceptIO "oracle/11"
    (mkRawCase15 "oracle/ok/8c/r2-bits9-ref3" (patternBits 56 2) 2 9 #[refA, refB, refD]))
  cases := cases.push (← fromExceptIO "oracle/12"
    (mkRawCase15 "oracle/ok/8c/r3-bits31-ref4-max" payload8cMax 3 31 #[refA, refB, refC, refD]))
  cases := cases.push (← fromExceptIO "oracle/13"
    (mkRawCase15 "oracle/ok/8c/deep-stack-preserve"
      (patternBits 17 4) 1 3 #[refD, refE] #[.slice (Slice.ofCell refC), .null]))

  -- Success: 8d family.
  cases := cases.push (← fromExceptIO "oracle/14"
    (mkRawCase18 "oracle/ok/8d/r0-len0-empty" #[] 0 0 #[]))
  cases := cases.push (← fromExceptIO "oracle/15"
    (mkRawCase18 "oracle/ok/8d/r1-len1-ref1" (patternBits 12 0) 1 1 #[refA]))
  cases := cases.push (← fromExceptIO "oracle/16"
    (mkRawCase18 "oracle/ok/8d/r2-len7-ref2" (patternBits 57 1) 2 7 #[refB, refD]))
  cases := cases.push (← fromExceptIO "oracle/17"
    (mkRawCase18 "oracle/ok/8d/r3-len31-ref3" (patternBits 200 2) 3 31 #[refA, refB, refC]))
  cases := cases.push (← fromExceptIO "oracle/18"
    (mkRawCase18 "oracle/ok/8d/r4-len31-ref4" (patternBits 222 3) 4 31 #[refA, refB, refC, refD]))
  cases := cases.push (← fromExceptIO "oracle/19"
    (mkRawCase18 "oracle/ok/8d/r0-len124-max-fit" payload8dMax 0 124 #[]))
  cases := cases.push (← fromExceptIO "oracle/20"
    (mkRawCase18 "oracle/ok/8d/deep-stack-preserve"
      (patternBits 31 0) 2 4 #[refD, refE] #[.null, intV 9, .slice (Slice.ofCell refB)]))

  -- Extra success coverage to keep a broad 30-case oracle batch.
  cases := cases.push (← fromExceptIO "oracle/21"
    (mkRawCase8 "oracle/ok/8b/len2-payload15" (patternBits 15 3) 2))
  cases := cases.push (← fromExceptIO "oracle/22"
    (mkRawCase8 "oracle/ok/8b/len0-empty-with-slice-below"
      #[] 0 #[.slice (Slice.ofCell refD)]))
  cases := cases.push (← fromExceptIO "oracle/23"
    (mkRawCase8 "oracle/ok/8b/tail-pushnull" (patternBits 63 1) 8 #[] #[] #[.pushNull]))

  cases := cases.push (← fromExceptIO "oracle/24"
    (mkRawCase15 "oracle/ok/8c/r0-bits0-ref1-with-int-below"
      #[] 0 0 #[refC] #[intV 123]))
  cases := cases.push (← fromExceptIO "oracle/25"
    (mkRawCase15 "oracle/ok/8c/r1-bits1-ref2" (patternBits 8 0) 1 1 #[refA, refE]))
  cases := cases.push (← fromExceptIO "oracle/26"
    (mkRawCase15 "oracle/ok/8c/r3-bits3-ref4" (patternBits 20 2) 3 3 #[refA, refB, refC, refD]))

  cases := cases.push (← fromExceptIO "oracle/27"
    (mkRawCase18 "oracle/ok/8d/r0-len1-altpayload" (patternBits 6 1) 0 1 #[]))
  cases := cases.push (← fromExceptIO "oracle/28"
    (mkRawCase18 "oracle/ok/8d/r1-len15-ref1" (patternBits 90 0) 1 15 #[refE]))
  cases := cases.push (← fromExceptIO "oracle/29"
    (mkRawCase18 "oracle/ok/8d/r2-len63-ref2" (patternBits 420 3) 2 63 #[refB, refD]))
  cases := cases.push (← fromExceptIO "oracle/30"
    (mkRawCase18 "oracle/ok/8d/r4-len0-ref4-empty"
      #[] 4 0 #[refA, refB, refC, refD] #[.null, .cell refE]))

  pure cases

initialize handcraftedOracleCasesCache : IO.Ref (Option (Array RawOracleCase)) ← IO.mkRef none

private def getHandcraftedOracleCases : IO (Array RawOracleCase) := do
  match (← handcraftedOracleCasesCache.get) with
  | some cases => pure cases
  | none =>
      let cases ← handcraftedOracleCases
      handcraftedOracleCasesCache.set (some cases)
      pure cases

private def runHandcraftedOracleCaseByIndex (idx : Nat) (expectedName : String) : IO Unit := do
  let cases ← getHandcraftedOracleCases
  let c ←
    match cases[idx]? with
    | some c => pure c
    | none =>
        failUnit
          s!"oracle/handcrafted/index-{idx}: expected `{expectedName}`, but only {cases.size} cases exist"
  if c.name != expectedName then
    failUnit s!"oracle/handcrafted/index-{idx}: expected `{expectedName}`, got `{c.name}`"
  runRawOracleBatchCompare s!"oracle/handcrafted/{expectedName}" #[c]

private def mkHandcraftedOracleUnitCase (idx : Nat) (caseName : String) : UnitCase :=
  { name := s!"unit/oracle/handcrafted/{caseName}"
    run := runHandcraftedOracleCaseByIndex idx caseName }

private def handcraftedOracleUnitCases : Array UnitCase := #[
  mkHandcraftedOracleUnitCase 0 "oracle/ok/8b/empty",
  mkHandcraftedOracleUnitCase 1 "oracle/ok/8b/bit1",
  mkHandcraftedOracleUnitCase 2 "oracle/ok/8b/trailing-zeros",
  mkHandcraftedOracleUnitCase 3 "oracle/ok/8b/max-len15-payload123",
  mkHandcraftedOracleUnitCase 4 "oracle/ok/8b/deep-stack-null",
  mkHandcraftedOracleUnitCase 5 "oracle/ok/8b/deep-stack-int-cell",
  mkHandcraftedOracleUnitCase 6 "oracle/ok/8b/prelude-and-tail",
  mkHandcraftedOracleUnitCase 7 "oracle/ok/8c/r0-bits0-ref1-empty",
  mkHandcraftedOracleUnitCase 8 "oracle/ok/8c/r0-bits1-ref1",
  mkHandcraftedOracleUnitCase 9 "oracle/ok/8c/r1-bits5-ref2",
  mkHandcraftedOracleUnitCase 10 "oracle/ok/8c/r2-bits9-ref3",
  mkHandcraftedOracleUnitCase 11 "oracle/ok/8c/r3-bits31-ref4-max",
  mkHandcraftedOracleUnitCase 12 "oracle/ok/8c/deep-stack-preserve",
  mkHandcraftedOracleUnitCase 13 "oracle/ok/8d/r0-len0-empty",
  mkHandcraftedOracleUnitCase 14 "oracle/ok/8d/r1-len1-ref1",
  mkHandcraftedOracleUnitCase 15 "oracle/ok/8d/r2-len7-ref2",
  mkHandcraftedOracleUnitCase 16 "oracle/ok/8d/r3-len31-ref3",
  mkHandcraftedOracleUnitCase 17 "oracle/ok/8d/r4-len31-ref4",
  mkHandcraftedOracleUnitCase 18 "oracle/ok/8d/r0-len124-max-fit",
  mkHandcraftedOracleUnitCase 19 "oracle/ok/8d/deep-stack-preserve",
  mkHandcraftedOracleUnitCase 20 "oracle/ok/8b/len2-payload15",
  mkHandcraftedOracleUnitCase 21 "oracle/ok/8b/len0-empty-with-slice-below",
  mkHandcraftedOracleUnitCase 22 "oracle/ok/8b/tail-pushnull",
  mkHandcraftedOracleUnitCase 23 "oracle/ok/8c/r0-bits0-ref1-with-int-below",
  mkHandcraftedOracleUnitCase 24 "oracle/ok/8c/r1-bits1-ref2",
  mkHandcraftedOracleUnitCase 25 "oracle/ok/8c/r3-bits3-ref4",
  mkHandcraftedOracleUnitCase 26 "oracle/ok/8d/r0-len1-altpayload",
  mkHandcraftedOracleUnitCase 27 "oracle/ok/8d/r1-len15-ref1",
  mkHandcraftedOracleUnitCase 28 "oracle/ok/8d/r2-len63-ref2",
  mkHandcraftedOracleUnitCase 29 "oracle/ok/8d/r4-len0-ref4-empty"
]

def suite : InstrSuite where
  id := { name := "PUSHSLICE" }
  unit := ( #[
    { name := "unit/direct/pushes-slice-and-preserves-stack"
      run := do
        let refA : Cell := Cell.empty
        let refB : Cell := Cell.ofUInt 1 1
        let s0 : Slice := Slice.ofCell Cell.empty
        let s1 : Slice := Slice.ofCell (Cell.mkOrdinary (natToBits 0b1011 4) #[refA])
        let s2 : Slice := Slice.ofCell (Cell.mkOrdinary (patternBits 29 2) #[refA, refB])
        let partialCell : Cell := Cell.mkOrdinary (patternBits 17 1) #[refA, refB]
        let sPartial : Slice := { cell := partialCell, bitPos := 3, refPos := 1 }

        expectOkStack "ok/empty-stack"
          (runPushSliceDirect (.pushSliceConst s0) #[])
          #[.slice s0]
        expectOkStack "ok/non-empty-stack-preserved"
          (runPushSliceDirect (.pushSliceConst s1) #[.null, intV 17])
          #[.null, intV 17, .slice s1]
        expectOkStack "ok/refs-and-bits-preserved"
          (runPushSliceDirect (.pushSliceConst s2) #[.cell refA])
          #[.cell refA, .slice s2]
        expectOkStack "ok/partial-slice-pushed-verbatim"
          (runPushSliceDirect (.pushSliceConst sPartial) #[.null])
          #[.null, .slice sPartial] }
    ,
    { name := "unit/dispatch/non-pushslice-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runPushSliceDispatchFallback .add #[])
          #[intV dispatchSentinel]
        expectOkStack "dispatch/pushref"
          (runPushSliceDispatchFallback (.pushRef Cell.empty) #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/pushcont"
          (runPushSliceDispatchFallback (.pushCont (Slice.ofCell Cell.empty)) #[intV 3])
          #[intV 3, intV dispatchSentinel] }
    ,
    { name := "unit/opcode/decode-cross-family-sequence"
      run := do
        let refA : Cell := Cell.empty
        let refB : Cell := Cell.ofUInt 1 1
        let (i8, c8) ← fromExceptIO "decode/8b"
          (mkPushSlice8InstrCode (natToBits 0x15 5) 1)
        let (i15, c15) ← fromExceptIO "decode/8c"
          (mkPushSlice15InstrCode (patternBits 12 1) 0 2 #[refA])
        let (i18, c18) ← fromExceptIO "decode/8d"
          (mkPushSlice18InstrCode (patternBits 21 2) 2 3 #[refA, refB])
        let addCell ← fromExceptIO "decode/add-cell" (assembleCode #[.add])
        let code ← fromExceptIO "decode/full-code" (do
          let x ← appendCodeCell c8 c15
          let y ← appendCodeCell x c18
          appendCodeCell y addCell)
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/step-8b" s0 i8 12
        let s2 ← expectDecodeStep "decode/step-8c" s1 i15 15
        let s3 ← expectDecodeStep "decode/step-8d" s2 i18 18
        let s4 ← expectDecodeStep "decode/step-add" s3 .add 8
        if s4.bitsRemaining = 0 ∧ s4.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/end: expected exhausted slice, got bits={s4.bitsRemaining}, refs={s4.refsRemaining}" }
    ,
    { name := "unit/opcode/decode-boundaries-per-family"
      run := do
        let refA : Cell := Cell.empty
        let refB : Cell := Cell.ofUInt 1 1
        let refC : Cell := Cell.ofUInt 2 2
        let refD : Cell := Cell.ofUInt 3 5

        let (i8min, c8min) ← fromExceptIO "decode/8b-min"
          (mkPushSlice8InstrCode #[] 0)
        let r8min ← expectDecodeStep "decode/8b-min" (Slice.ofCell c8min) i8min 12
        if r8min.bitsRemaining = 0 ∧ r8min.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/8b-min: expected exhausted slice, got bits={r8min.bitsRemaining}, refs={r8min.refsRemaining}"

        let (i8max, c8max) ← fromExceptIO "decode/8b-max"
          (mkPushSlice8InstrCode (patternBits 123 0) 15)
        let r8max ← expectDecodeStep "decode/8b-max" (Slice.ofCell c8max) i8max 12
        if r8max.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/8b-max: expected exhausted bits, got {r8max.bitsRemaining}"

        let zeroRaw8 ← fromExceptIO "decode/8b-all-zero-raw"
          (mkPushSlice8CodeFromRaw 0 (Array.replicate (pushSliceDataBits8 0) false))
        let zeroInstr : Instr := .pushSliceConst (Slice.ofCell Cell.empty)
        let rz ← expectDecodeStep "decode/8b-all-zero-raw" (Slice.ofCell zeroRaw8) zeroInstr 12
        if rz.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/8b-all-zero-raw: expected exhausted bits, got {rz.bitsRemaining}"

        let (i15max, c15max) ← fromExceptIO "decode/8c-max"
          (mkPushSlice15InstrCode (patternBits 248 1) 3 31 #[refA, refB, refC, refD])
        let r15max ← expectDecodeStep "decode/8c-max" (Slice.ofCell c15max) i15max 15
        if r15max.bitsRemaining = 0 ∧ r15max.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/8c-max: expected exhausted slice, got bits={r15max.bitsRemaining}, refs={r15max.refsRemaining}"

        let (i18max, c18max) ← fromExceptIO "decode/8d-max-fit"
          (mkPushSlice18InstrCode (patternBits 997 2) 0 124 #[])
        let r18max ← expectDecodeStep "decode/8d-max-fit" (Slice.ofCell c18max) i18max 18
        if r18max.bitsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/8d-max-fit: expected exhausted bits, got {r18max.bitsRemaining}" }
    ,
    { name := "unit/opcode/decode-invalid-refs-and-truncation"
      run := do
        let invalidRefs5 ← fromExceptIO "decode/refs5"
          (mkPushSlice18CodeFromRaw 5 0 #[] #[])
        let invalidRefs7 ← fromExceptIO "decode/refs7"
          (mkPushSlice18CodeFromRaw 7 0 #[] #[])
        let trunc8 ← fromExceptIO "decode/trunc8" (mkTruncated8Code 1)
        let trunc15 ← fromExceptIO "decode/trunc15" (mkTruncated15Code 1 4)
        let trunc18 ← fromExceptIO "decode/trunc18" (mkTruncated18Code 2 7)
        let miss15 ← fromExceptIO "decode/miss15" (mkMissingRefs15Code 3 2)
        let miss18 ← fromExceptIO "decode/miss18" (mkMissingRefs18Code 4 1)
        let bitsBeforeRefs ← fromExceptIO "decode/bits-before-refs"
          (mkPushSlice18CodeFromRaw 4 31 (Array.replicate 10 false) #[])

        expectDecodeInvOpcode "decode/8d-invalid-refs5" (Slice.ofCell invalidRefs5)
        expectDecodeInvOpcode "decode/8d-invalid-refs7" (Slice.ofCell invalidRefs7)
        expectDecodeInvOpcode "decode/8b-truncated" (Slice.ofCell trunc8)
        expectDecodeInvOpcode "decode/8c-truncated" (Slice.ofCell trunc15)
        expectDecodeInvOpcode "decode/8d-truncated" (Slice.ofCell trunc18)
        expectDecodeInvOpcode "decode/8c-missing-refs" (Slice.ofCell miss15)
        expectDecodeInvOpcode "decode/8d-missing-refs" (Slice.ofCell miss18)
        expectDecodeInvOpcode "decode/8d-bits-before-refs" (Slice.ofCell bitsBeforeRefs) }
    ,
    { name := "unit/opcode/assembler-rejects-pushsliceconst"
      run := do
        let instr : Instr := .pushSliceConst (Slice.ofCell Cell.empty)
        match assembleCp0 [instr] with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"assemble/pushsliceconst: expected invOpcode, got {e}"
        | .ok _ => failUnit "assemble/pushsliceconst: expected invOpcode, got success" }
    ,
    { name := "unit/gas/exact-and-minus-one"
      run := do
        let (_, code) ← fromExceptIO "gas/code"
          (mkPushSlice8InstrCode (natToBits 0x0d 4) 1)
        let initStack : Array Value := #[.null]
        let baseline := runCodeVm code initStack 1_000_000 1_000_000
        let baselineState ← expectExitCode "gas/baseline-success" (~~~ 0) baseline
        let exact := baselineState.gas.gasConsumed
        if exact ≤ 0 then
          failUnit s!"gas/exact: expected positive gas, got {exact}"
        else
          pure ()

        let exactRes := runCodeVm code initStack exact exact
        let _ ← expectExitCode "gas/exact-success" (~~~ 0) exactRes

        let minus := exact - 1
        let minusRes := runCodeVm code initStack minus minus
        let _ ← expectExitCode "gas/exact-minus-one-out-of-gas" Excno.outOfGas.toInt minusRes
        pure () }
    ,
    { name := "unit/oracle/handcrafted-30"
      run := do
        let cases ← getHandcraftedOracleCases
        if cases.size != 30 then
          failUnit s!"oracle/handcrafted: expected 30 cases, got {cases.size}"
        runRawOracleBatchCompare "oracle/handcrafted" cases }
  ] ++ handcraftedOracleUnitCases)
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHSLICE
