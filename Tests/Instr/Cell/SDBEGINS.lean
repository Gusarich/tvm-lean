import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index
import TvmLean.Validation.Canon.Result
import TvmLean.Validation.Oracle.Report
import TvmLean.Validation.Oracle.Runner

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDBEGINS

/-
SDBEGINS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdBeginsConst.lean` (`.sdBeginsConst quiet pref`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (13-bit ext prefix `0xd728 >> 3`, args8 `{quiet,lenTag}`, `bitsStripTrailingMarker`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.sdBeginsConst` intentionally not assemblable via `assembleCp0`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_begins_with_common`, `exec_slice_begins_with_const`, opcode ext table).

Branch map covered by this suite:
- execute dispatch: `.sdBeginsConst` handled vs fallback to `next`;
- stack path: one `popSlice` (underflow/type on top stack element);
- predicate split: `s` begins with const prefix bits vs mismatch;
- quiet split: on mismatch (`quiet=false` -> `cellUnd`; `quiet=true` -> restore `s` + push `0`);
- success split: push remainder slice, and for quiet also push `-1`;
- decode path: ext-prefix/args/payload marker stripping, plus truncation `invOpcode` and
  neighboring `SDBEGINSX/SDBEGINSXQ` boundary.
-/

private def sdbeginsId : InstrId := { name := "SDBEGINS" }

private def sdbeginsPrefix13 : Nat := 0xd728 >>> 3
private def sdbeginsXWord : Nat := 0xd726
private def sdbeginsXQWord : Nat := 0xd727

private def dispatchSentinel : Int := 13770

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def fromExceptIO {α} (label : String) (res : Except String α) : IO α := do
  match res with
  | .ok v => pure v
  | .error e => failUnit s!"{label}: {e}"

private def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkSdbeginsInstrFromBits (quiet : Bool) (prefBits : BitString) : Instr :=
  .sdBeginsConst quiet (mkSliceWithBitsRefs prefBits)

private def runSdbeginsDirect
    (quiet : Bool)
    (pref : Slice)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdBeginsConst (.sdBeginsConst quiet pref) stack

private def runSdbeginsDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellSdBeginsConst
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok lv, .ok rv => lv == rv
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    failUnit s!"{label}: expected same outcome, lhs={reprStr lhs}, rhs={reprStr rhs}"

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        failUnit s!"{label}: expected decode error {expected}, got {e}"
  | .ok (instr, bits, _) =>
      failUnit s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}"

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

private def minLenTagForPayload (payloadBits : Nat) : Nat :=
  let need := payloadBits + 1
  if need ≤ 3 then
    0
  else
    (need - 3 + 7) / 8

private def sdbeginsDataBits (lenTag : Nat) : Nat :=
  lenTag * 8 + 3

private def encodeRawWithMarker (payload : BitString) (lenTag : Nat) : Except String BitString := do
  if lenTag > 127 then
    throw s!"lenTag out of range: {lenTag}"
  let dataBits := sdbeginsDataBits lenTag
  if payload.size + 1 > dataBits then
    throw s!"payload too large for lenTag={lenTag}: payload={payload.size} bits, max={dataBits - 1}"
  pure (payload ++ #[true] ++ Array.replicate (dataBits - payload.size - 1) false)

private def mkSdbeginsCoreBits
    (payload : BitString)
    (quiet : Bool)
    (lenTag : Nat) : Except String BitString := do
  let raw ← encodeRawWithMarker payload lenTag
  let args8 : Nat := (if quiet then 0x80 else 0) + lenTag
  let word21 : Nat := (sdbeginsPrefix13 <<< 8) + args8
  pure (natToBits word21 21 ++ raw)

private def appendCodeCell (a b : Cell) : Except String Cell := do
  if a.bits.size + b.bits.size > 1023 then
    throw "code append overflow (bits > 1023)"
  if a.refs.size + b.refs.size > 4 then
    throw "code append overflow (refs > 4)"
  pure (Cell.mkOrdinary (a.bits ++ b.bits) (a.refs ++ b.refs))

private def assembleCode (program : Array Instr) : Except String Cell := do
  if program.isEmpty then
    pure Cell.empty
  else
    match assembleCp0 program.toList with
    | .ok c => pure c
    | .error e => throw s!"assembleCp0 failed: {e}"

private def mkSdbeginsCode
    (payload : BitString)
    (quiet : Bool)
    (lenTag : Nat)
    (init : Array Instr := #[])
    (tail : Array Instr := #[]) : Except String (Instr × Cell) := do
  let coreBits ← mkSdbeginsCoreBits payload quiet lenTag
  let initCode ← assembleCode init
  let tailCode ← assembleCode tail
  let core : Cell := Cell.mkOrdinary coreBits #[]
  let withCore ← appendCodeCell initCode core
  let full ← appendCodeCell withCore tailCode
  pure (mkSdbeginsInstrFromBits quiet payload, full)

private def mkSdbeginsCodeAuto
    (payload : BitString)
    (quiet : Bool)
    (init : Array Instr := #[])
    (tail : Array Instr := #[]) : Except String (Instr × Cell) :=
  mkSdbeginsCode payload quiet (minLenTagForPayload payload.size) init tail

private def mkSdbeginsMalformedTruncatedDataCode
    (payload : BitString)
    (quiet : Bool)
    (lenTag : Nat) : Except String Cell := do
  let coreBits ← mkSdbeginsCoreBits payload quiet lenTag
  if coreBits.size = 0 then
    throw "unexpected empty core bits"
  pure (Cell.mkOrdinary (coreBits.take (coreBits.size - 1)) #[])

private def toBocHex (c : Cell) : Except String String := do
  let bytes ←
    match stdBocSerialize c with
    | .ok b => pure b
    | .error e => throw s!"stdBocSerialize failed: {reprStr e}"
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

private structure RawOracleCase where
  name : String
  code : Cell
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

private def runRawOracleCase (c : RawOracleCase) : IO Unit := do
  let stackTokens ←
    match stackToOracleTokens c.initStack with
    | .ok toks => pure toks
    | .error e => failUnit s!"{c.name}: {e}"

  let leanCanon ←
    match leanCanonResult (TvmLeanOracleValidate.runLean c.code c.initStack c.fuel) with
    | .ok result => pure result
    | .error e => failUnit s!"{c.name}: {e}"

  let oracleOut ←
    try
      TvmLeanOracleValidate.runOracle c.code stackTokens
    catch e =>
      failUnit s!"{c.name}: oracle run failed: {e.toString}"

  let oracleCanon : CanonResult :=
    CanonResult.ofOracleRaw
      oracleOut.exitRaw
      oracleOut.gasUsed
      oracleOut.c4Hash
      oracleOut.c5Hash
      oracleOut.stackTop

  let cmp := compareCanonResults leanCanon oracleCanon
  if cmp.ok then
    pure ()
  else
    let reason :=
      match cmp.mismatch? with
      | some m => m.message
      | none => "oracle comparison failed"
    failUnit s!"{c.name}: {reason}"

private def mkRawCase
    (name : String)
    (payload : BitString)
    (quiet : Bool)
    (lenTag : Nat)
    (initStack : Array Value := #[])
    (init : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase := do
  let (_, code) ← mkSdbeginsCode payload quiet lenTag init tail
  pure { name, code, initStack, fuel }

private def mkRawCaseAuto
    (name : String)
    (payload : BitString)
    (quiet : Bool)
    (initStack : Array Value := #[])
    (init : Array Instr := #[])
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase :=
  mkRawCase name payload quiet (minLenTagForPayload payload.size) initStack init tail fuel

private def popSliceFromValue (v : Value) : Except Excno Slice := do
  match v with
  | .slice s => pure s
  | _ => throw .typeChk

private def runSdbeginsModel
    (quiet : Bool)
    (pref : Slice)
    (stack : Array Value) : Except Excno (Array Value) := do
  if stack.isEmpty then
    throw .stkUnd
  let sVal := stack.back!
  let below := stack.pop
  let s ← popSliceFromValue sVal
  let prefBits := pref.readBits pref.bitsRemaining
  let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
  if ok then
    let out := below.push (.slice (s.advanceBits prefBits.size))
    if quiet then
      pure (out.push (intV (-1)))
    else
      pure out
  else
    if quiet then
      pure ((below.push (.slice s)).push (intV 0))
    else
      throw .cellUnd

private def randBitString (n : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:n] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def fuzzRefPool : Array Cell :=
  #[
    Cell.empty,
    Cell.mkOrdinary (natToBits 5 3) #[],
    Cell.mkOrdinary (natToBits 11 4) #[],
    Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]
  ]

private def pickRefFromPool (rng0 : StdGen) : Cell × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzRefPool.size - 1)
  (fuzzRefPool[idx]!, rng1)

private def genRefs (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut out : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (c, rng') := pickRefFromPool rng
    out := out.push c
    rng := rng'
  return (out, rng)

private def fuzzBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 31, 32, 47, 48, 63, 64, 95, 96]

private def pickFuzzBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    let (idx, rng2) := randNat rng1 0 (fuzzBitsBoundaryPool.size - 1)
    (fuzzBitsBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 96

private def genRandomSlice (rng0 : StdGen) : Slice × StdGen :=
  let (totalBits, rng1) := pickFuzzBitsMixed rng0
  let (totalRefs, rng2) := randNat rng1 0 3
  let (bits, rng3) := randBitString totalBits rng2
  let (refs, rng4) := genRefs totalRefs rng3
  let cell : Cell := Cell.mkOrdinary bits refs
  let (shape, rng5) := randNat rng4 0 4
  if shape ≤ 2 then
    (Slice.ofCell cell, rng5)
  else
    let (bitPos, rng6) := randNat rng5 0 totalBits
    let (refPos, rng7) := randNat rng6 0 totalRefs
    ({ cell, bitPos, refPos }, rng7)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 4
  if k = 0 then
    (.null, rng1)
  else if k = 1 then
    let (n, rng2) := randNat rng1 0 200
    (intV (Int.ofNat n - 100), rng2)
  else if k = 2 then
    (.cell Cell.empty, rng1)
  else if k = 3 then
    (.builder Builder.empty, rng1)
  else
    (.slice (Slice.ofCell Cell.empty), rng1)

private def genSdbeginsDirectFuzzInput
    (rng0 : StdGen) : (Bool × Slice × Array Value) × StdGen :=
  let (quiet, rng1) := randBool rng0
  let (pref, rng2) := genRandomSlice rng1
  let (shape, rng3) := randNat rng2 0 9
  if shape = 0 then
    ((quiet, pref, #[]), rng3)
  else if shape = 1 then
    ((quiet, pref, #[.null]), rng3)
  else if shape = 2 then
    let (n, rng4) := randNat rng3 0 40
    ((quiet, pref, #[intV (Int.ofNat n - 20)]), rng4)
  else if shape = 3 then
    ((quiet, pref, #[.cell Cell.empty]), rng3)
  else if shape = 4 then
    ((quiet, pref, #[.builder Builder.empty]), rng3)
  else
    let (s, rng4) := genRandomSlice rng3
    if shape = 5 then
      ((quiet, pref, #[.slice s]), rng4)
    else
      let (noise, rng5) := pickNoiseValue rng4
      ((quiet, pref, #[noise, .slice s]), rng5)

private def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def refLeafB : Cell := Cell.mkOrdinary (natToBits 11 4) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[refLeafA]

private def bitsA8 : BitString := natToBits 0xa5 8
private def bitsB8 : BitString := natToBits 0x25 8
private def bitsC8 : BitString := natToBits 0xad 8
private def bits16A : BitString := natToBits 0x9bcd 16
private def bits40A : BitString := stripeBits 40 0
private def bits40B : BitString := stripeBits 40 1
private def bits120A : BitString := stripeBits 120 0
private def bits120B : BitString := stripeBits 120 1

private def prefBitsA3 : BitString := bitsA8.extract 0 3
private def prefBitsA5 : BitString := bitsA8.extract 0 5
private def prefBitsA5FirstMismatch : BitString := natToBits 0x04 5
private def prefBitsA5MidMismatch : BitString := natToBits 0x16 5
private def prefBits16Head9 : BitString := bits16A.extract 0 9
private def prefBits40Head31 : BitString := bits40A.extract 0 31
private def prefBits120Head95 : BitString := bits120A.extract 0 95

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def sliceA8 : Slice := mkSliceWithBitsRefs bitsA8
private def sliceA8WithRefs : Slice := mkSliceWithBitsRefs bitsA8 #[refLeafA, refLeafB]
private def sliceB8 : Slice := mkSliceWithBitsRefs bitsB8
private def sliceC8 : Slice := mkSliceWithBitsRefs bitsC8
private def slice16A : Slice := mkSliceWithBitsRefs bits16A
private def slice15From16A : Slice := mkSliceWithBitsRefs (bits16A.extract 0 15)
private def slice40A : Slice := mkSliceWithBitsRefs bits40A
private def slice40B : Slice := mkSliceWithBitsRefs bits40B
private def slice120A : Slice := mkSliceWithBitsRefs bits120A
private def slice120B : Slice := mkSliceWithBitsRefs bits120B

private def prefEmpty : Slice := mkSliceWithBitsRefs #[]
private def prefA3 : Slice := mkSliceWithBitsRefs prefBitsA3
private def prefA5 : Slice := mkSliceWithBitsRefs prefBitsA5
private def prefA5WithRefs : Slice := mkSliceWithBitsRefs prefBitsA5 #[refLeafC]
private def prefA5FirstMismatch : Slice := mkSliceWithBitsRefs prefBitsA5FirstMismatch
private def prefA5MidMismatch : Slice := mkSliceWithBitsRefs prefBitsA5MidMismatch
private def pref16Head9 : Slice := mkSliceWithBitsRefs prefBits16Head9
private def pref40Head31 : Slice := mkSliceWithBitsRefs prefBits40Head31
private def pref120Head95 : Slice := mkSliceWithBitsRefs prefBits120Head95

private def cursorCell : Cell :=
  Cell.mkOrdinary (stripeBits 29 1) #[refLeafA, refLeafB, refLeafC]

private def cursorSubject : Slice :=
  { cell := cursorCell, bitPos := 4, refPos := 1 }

private def cursorPref : Slice :=
  mkSliceWithBitsRefs (cursorSubject.readBits 7) #[refLeafA]

private def cursorPrefMismatch : Slice :=
  mkSliceWithBitsRefs (natToBits 0 7)

private def buildRawOracleCases : Except String (Array RawOracleCase) := do
  let mut cases : Array RawOracleCase := #[]

  -- Success paths (non-quiet).
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/empty-empty" #[] false #[.slice sliceEmpty])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/empty-prefix-a8" #[] false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/exact-a8" bitsA8 false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/prefix3-a8" prefBitsA3 false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/prefix5-a8" prefBitsA5 false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/prefix9-16" prefBits16Head9 false #[.slice slice16A])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/prefix31-40" prefBits40Head31 false #[.slice slice40A])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/refs-ignored" prefBitsA5 false #[.slice sliceA8WithRefs])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/deep-null" prefBitsA5 false #[.null, .slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/nonquiet/deep-int" prefBits16Head9 false #[intV 77, .slice slice16A])

  -- Success paths (quiet=true).
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/empty-prefix-a8" #[] true #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/exact-a8" bitsA8 true #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/prefix3-a8" prefBitsA3 true #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/prefix31-40" prefBits40Head31 true #[.slice slice40A])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/deep-null" prefBits16Head9 true #[.null, .slice slice16A])

  -- Mismatch paths: non-quiet throws `cellUnd`.
  cases := cases.push (← mkRawCaseAuto "oracle/err/nonquiet/first-bit-mismatch" prefBitsA5FirstMismatch false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/err/nonquiet/mid-bit-mismatch" prefBitsA5MidMismatch false #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/err/nonquiet/short-slice" bitsA8 false #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7))])
  cases := cases.push (← mkRawCaseAuto "oracle/err/nonquiet/nonempty-vs-empty" prefBitsA3 false #[.slice sliceEmpty])
  cases := cases.push (← mkRawCaseAuto "oracle/err/nonquiet/prefix16-vs-15" bits16A false #[.slice slice15From16A])

  -- Mismatch paths: quiet restores input slice and pushes `0`.
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/first-bit-mismatch" prefBitsA5FirstMismatch true #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/mid-bit-mismatch" prefBitsA5MidMismatch true #[.slice sliceA8])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/short-slice" bitsA8 true #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7))])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/nonempty-vs-empty" prefBitsA3 true #[.slice sliceEmpty])
  cases := cases.push (← mkRawCaseAuto "oracle/ok/quiet/deep-mismatch" prefBitsA5FirstMismatch true #[intV (-8), .slice sliceA8])

  -- Stack underflow/type paths.
  cases := cases.push (← mkRawCaseAuto "oracle/err/underflow/empty" prefBitsA3 false #[])
  cases := cases.push (← mkRawCaseAuto "oracle/err/type/top-null" prefBitsA3 false #[.null])
  cases := cases.push (← mkRawCaseAuto "oracle/err/type/top-int" prefBitsA3 false #[intV 1])
  cases := cases.push (← mkRawCaseAuto "oracle/err/type/top-cell" prefBitsA3 false #[.cell Cell.empty])

  -- Additional long-prefix quiet mismatch (keeps stack + pushes 0).
  cases := cases.push
    (← mkRawCaseAuto "oracle/ok/quiet/long-mismatch"
      prefBits120Head95 true #[.slice slice120B])

  pure cases

private def rawOracleUnitCases : Array UnitCase :=
  match buildRawOracleCases with
  | .ok cases =>
      if cases.size = 30 then
        cases.map fun c =>
          { name := s!"unit/raw-oracle/{c.name}"
            run := runRawOracleCase c }
      else
        #[
          { name := "unit/raw-oracle/spec-count-mismatch"
            run := failUnit s!"raw-oracle: expected exactly 30 cases, got {cases.size}" }
        ]
  | .error e =>
      #[
        { name := "unit/raw-oracle/spec-build-error"
          run := failUnit s!"raw-oracle: failed to build handcrafted cases: {e}" }
      ]

def suite : InstrSuite where
  id := { name := "SDBEGINS" }
  unit := #[
    { name := "unit/direct/success-edge-and-cursor"
      run := do
        expectOkStack "ok/nonquiet/exact-a8"
          (runSdbeginsDirect false (mkSliceWithBitsRefs bitsA8) #[.slice sliceA8])
          #[.slice (sliceA8.advanceBits 8)]

        expectOkStack "ok/nonquiet/proper-prefix5"
          (runSdbeginsDirect false prefA5 #[.slice sliceA8])
          #[.slice (sliceA8.advanceBits prefA5.bitsRemaining)]

        expectOkStack "ok/nonquiet/empty-prefix-keeps-s"
          (runSdbeginsDirect false prefEmpty #[.slice sliceA8])
          #[.slice sliceA8]

        expectOkStack "ok/nonquiet/refs-ignored-in-prefix"
          (runSdbeginsDirect false prefA5WithRefs #[.slice sliceA8WithRefs])
          #[.slice (sliceA8WithRefs.advanceBits prefA5WithRefs.bitsRemaining)]

        expectOkStack "ok/quiet/exact-a8"
          (runSdbeginsDirect true (mkSliceWithBitsRefs bitsA8) #[.slice sliceA8])
          #[.slice (sliceA8.advanceBits 8), intV (-1)]

        expectOkStack "ok/quiet/empty-prefix"
          (runSdbeginsDirect true prefEmpty #[.slice sliceA8])
          #[.slice sliceA8, intV (-1)]

        expectOkStack "ok/nonquiet/cursor-prefix"
          (runSdbeginsDirect false cursorPref #[.slice cursorSubject])
          #[.slice (cursorSubject.advanceBits cursorPref.bitsRemaining)]

        expectOkStack "ok/nonquiet/deep-stack-preserve-below"
          (runSdbeginsDirect false prefA5 #[.null, intV 17, .slice sliceA8])
          #[.null, intV 17, .slice (sliceA8.advanceBits prefA5.bitsRemaining)] }
    ,
    { name := "unit/direct/mismatch-quiet-vs-nonquiet"
      run := do
        expectErr "err/nonquiet/first-bit-mismatch"
          (runSdbeginsDirect false prefA5FirstMismatch #[.slice sliceA8]) .cellUnd

        expectErr "err/nonquiet/mid-bit-mismatch"
          (runSdbeginsDirect false prefA5MidMismatch #[.slice sliceA8]) .cellUnd

        expectErr "err/nonquiet/short-s"
          (runSdbeginsDirect false (mkSliceWithBitsRefs bitsA8)
            #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7))]) .cellUnd

        expectErr "err/nonquiet/nonempty-vs-empty"
          (runSdbeginsDirect false prefA3 #[.slice sliceEmpty]) .cellUnd

        expectOkStack "ok/quiet/first-bit-mismatch"
          (runSdbeginsDirect true prefA5FirstMismatch #[.slice sliceA8])
          #[.slice sliceA8, intV 0]

        expectOkStack "ok/quiet/mid-bit-mismatch"
          (runSdbeginsDirect true prefA5MidMismatch #[.slice sliceA8])
          #[.slice sliceA8, intV 0]

        expectOkStack "ok/quiet/short-s"
          (runSdbeginsDirect true (mkSliceWithBitsRefs bitsA8)
            #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7))])
          #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7)), intV 0]

        expectOkStack "ok/quiet/cursor-mismatch"
          (runSdbeginsDirect true cursorPrefMismatch #[.slice cursorSubject])
          #[.slice cursorSubject, intV 0]

        expectOkStack "ok/quiet/deep-stack-mismatch"
          (runSdbeginsDirect true prefA5FirstMismatch #[intV (-3), .slice sliceA8])
          #[intV (-3), .slice sliceA8, intV 0] }
    ,
    { name := "unit/direct/underflow-type-order-and-dispatch"
      run := do
        expectErr "underflow/empty"
          (runSdbeginsDirect false prefA3 #[]) .stkUnd

        expectErr "type/top-null"
          (runSdbeginsDirect false prefA3 #[.null]) .typeChk

        expectErr "type/top-int"
          (runSdbeginsDirect false prefA3 #[intV 7]) .typeChk

        expectErr "type/top-cell"
          (runSdbeginsDirect false prefA3 #[.cell Cell.empty]) .typeChk

        expectErr "type/top-builder"
          (runSdbeginsDirect false prefA3 #[.builder Builder.empty]) .typeChk

        expectOkStack "dispatch/fallback-add"
          (runSdbeginsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        expectOkStack "dispatch/fallback-sdbeginsx"
          (runSdbeginsDispatchFallback (.sdBeginsX false) #[intV 12])
          #[intV 12, intV dispatchSentinel] }
    ,
    { name := "unit/model/alignment-representative-samples"
      run := do
        let samples : Array (String × Bool × Slice × Array Value) :=
          #[("ok/nonquiet/exact", false, mkSliceWithBitsRefs bitsA8, #[.slice sliceA8]),
            ("ok/nonquiet/prefix", false, prefA5, #[.slice sliceA8]),
            ("ok/quiet/prefix", true, prefA5, #[.slice sliceA8]),
            ("ok/quiet/empty-prefix", true, prefEmpty, #[.slice sliceA8]),
            ("ok/nonquiet/cursor", false, cursorPref, #[.slice cursorSubject]),
            ("err/nonquiet/mismatch", false, prefA5FirstMismatch, #[.slice sliceA8]),
            ("ok/quiet/mismatch", true, prefA5MidMismatch, #[.slice sliceA8]),
            ("err/nonquiet/short", false, mkSliceWithBitsRefs bitsA8, #[.slice (mkSliceWithBitsRefs (bitsA8.extract 0 7))]),
            ("err/underflow", false, prefA3, #[]),
            ("err/type/null", false, prefA3, #[.null]),
            ("err/type/int", true, prefA3, #[intV 11]),
            ("ok/deep/preserve", true, prefA3, #[.null, .slice sliceA8])]

        for (label, quiet, pref, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runSdbeginsDirect quiet pref stack)
            (runSdbeginsModel quiet pref stack) }
    ,
    { name := "unit/opcode/decode-boundaries-and-marker-stripping"
      run := do
        let payloadMain : BitString := prefBitsA5
        let payloadLong : BitString := prefBits120Head95

        let (instrMain, codeMain) ← fromExceptIO "decode/main"
          (mkSdbeginsCode payloadMain false 1 #[] #[.add])
        let d0 := Slice.ofCell codeMain
        let d1 ← expectDecodeStep "decode/main/sdbegins" d0 instrMain 21
        let d2 ← expectDecodeStep "decode/main/tail-add" d1 .add 8
        if d2.bitsRemaining = 0 ∧ d2.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/main/end: expected exhausted slice, got bits={d2.bitsRemaining}, refs={d2.refsRemaining}"

        let (instrLong, codeLong) ← fromExceptIO "decode/long"
          (mkSdbeginsCode payloadLong true 12)
        let dl ← expectDecodeStep "decode/long/sdbeginsq" (Slice.ofCell codeLong) instrLong 21
        if dl.bitsRemaining = 0 ∧ dl.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/long/end: expected exhausted slice, got bits={dl.bitsRemaining}, refs={dl.refsRemaining}"

        let coreA ← fromExceptIO "decode/seq/core-a" (mkSdbeginsCoreBits payloadMain false 1)
        let coreQ ← fromExceptIO "decode/seq/core-q" (mkSdbeginsCoreBits #[] true 0)
        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => failUnit s!"decode/seq/assemble-add failed: {e}"

        let seqBits : BitString :=
          natToBits sdbeginsXWord 16 ++
          natToBits sdbeginsXQWord 16 ++
          coreA ++ coreQ ++ addCell.bits

        let s0 := mkSliceFromBits seqBits
        let s1 ← expectDecodeStep "decode/seq/sdbeginsx" s0 (.sdBeginsX false) 16
        let s2 ← expectDecodeStep "decode/seq/sdbeginsxq" s1 (.sdBeginsX true) 16
        let s3 ← expectDecodeStep "decode/seq/sdbegins" s2 (mkSdbeginsInstrFromBits false payloadMain) 21
        let s4 ← expectDecodeStep "decode/seq/sdbeginsq" s3 (mkSdbeginsInstrFromBits true #[]) 21
        let s5 ← expectDecodeStep "decode/seq/add" s4 .add 8
        if s5.bitsRemaining = 0 ∧ s5.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/seq/end: expected exhausted slice, got bits={s5.bitsRemaining}, refs={s5.refsRemaining}" }
    ,
    { name := "unit/opcode/decode-invalid-and-assembler-reject"
      run := do
        let assembleInstr : Instr := mkSdbeginsInstrFromBits false prefBitsA3
        match assembleCp0 [assembleInstr] with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"assemble/sdbegins: expected invOpcode, got {e}"
        | .ok _ => failUnit "assemble/sdbegins: expected invOpcode, got success"

        let headerOnly : BitString := (natToBits ((sdbeginsPrefix13 <<< 8) + 0x01) 21).take 20
        expectDecodeErr "decode/invalid/truncated-header" (mkSliceFromBits headerOnly) .invOpcode

        let raw11 ← fromExceptIO "decode/invalid/raw11" (encodeRawWithMarker prefBitsA5 1)
        let brokenDataBits : BitString :=
          natToBits ((sdbeginsPrefix13 <<< 8) + 0x01) 21 ++ raw11.take (raw11.size - 2)
        expectDecodeErr "decode/invalid/truncated-data" (mkSliceFromBits brokenDataBits) .invOpcode

        let zeroRawCode ← fromExceptIO "decode/zero-raw" do
          mkSdbeginsCode #[] false 0
        let (zeroInstr, zeroCode) := zeroRawCode
        let z1 ← expectDecodeStep "decode/zero-raw/sdbegins" (Slice.ofCell zeroCode) zeroInstr 21
        if z1.bitsRemaining = 0 ∧ z1.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/zero-raw/end: expected exhausted slice, got bits={z1.bitsRemaining}, refs={z1.refsRemaining}"

        let malformed ← fromExceptIO "decode/invalid/malformed" (mkSdbeginsMalformedTruncatedDataCode prefBitsA5 false 1)
        expectDecodeErr "decode/invalid/malformed-inline" (Slice.ofCell malformed) .invOpcode

        expectDecodeErr "decode/invalid/short-12bits"
          (mkSliceFromBits (natToBits (sdbeginsPrefix13 >>> 1) 12)) .invOpcode }
    ,
    { name := "unit/fuzz/direct-model-seeded-280"
      run := do
        let seed : UInt64 := 2026021018
        let count : Nat := 280
        let mut rng := mkStdGen seed.toNat
        for i in [0:count] do
          let ((quiet, pref, stack), rng') := genSdbeginsDirectFuzzInput rng
          rng := rng'
          let got := runSdbeginsDirect quiet pref stack
          let want := runSdbeginsModel quiet pref stack
          match got, want with
          | .ok gs, .ok ws =>
              if gs == ws then
                pure ()
              else
                failUnit
                  s!"fuzz/{i}/stack-mismatch\nquiet={quiet}\npref={reprStr pref}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}"
          | .error ge, .error we =>
              if ge == we then
                pure ()
              else
                failUnit
                  s!"fuzz/{i}/error-mismatch\nquiet={quiet}\npref={reprStr pref}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}"
          | _, _ =>
              failUnit
                s!"fuzz/{i}/kind-mismatch\nquiet={quiet}\npref={reprStr pref}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}" }
  ] ++ rawOracleUnitCases
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDBEGINS
