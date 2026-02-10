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

namespace Tests.Instr.Cell.STSLICECONST

/-
STSLICECONST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSliceConst.lean` (`.stSliceConst`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (9-bit prefix decode with inline payload)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.stSliceConst` currently rejects assembly with `.invOpcode`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_const_slice`, `dump_store_const_slice`, registration at `0xcf80>>7`).

Branch map used for this suite:
- Lean exec path: 5 branch sites / 6 terminal outcomes
  (`.stSliceConst` dispatch; `popBuilder` underflow/type/success;
   capacity guard `canExtendBy(bits,refs)`; success push; overflow throw).
- C++ exec path: 5 branch sites / 6 aligned outcomes
  (`check_underflow(1)`; `pop_builder`; `check_space`; append slice; `cell_ov` throw).
- Decode path (Lean/C++ aligned):
  9-bit prefix + 5-bit args, then `dataBits=(len*8+2)` and `refs`,
  with early `inv_opcode` on insufficient bits/refs.

Key risk areas:
- inline payload uses trailing-marker encoding (`remove_trailing`/`bitsStripTrailingMarker`);
- opcode consumes only 14 prefix bits for gas/decode accounting, while payload comes from code slice tail;
- no quiet variant: overflow is always throwing (`cellOv`);
- decode guards (`invOpcode`) must fire before any stack/type behavior.
-/

private def stSliceConstId : InstrId := { name := "STSLICECONST" }

private def stSliceConstPrefix9 : Nat := 0xcf80 >>> 7

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def fromExceptIO {α} (label : String) (res : Except String α) : IO α := do
  match res with
  | .ok v => pure v
  | .error e => failUnit s!"{label}: {e}"

private def stSliceConstDataBits (lenTag : Nat) : Nat :=
  lenTag * 8 + 2

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
    | .error e => throw s!"assemble failed: {e}"

private def encodeRawWithMarker (payload : BitString) (lenTag : Nat) : Except String BitString := do
  if lenTag > 7 then
    throw s!"lenTag out of range: {lenTag}"
  let dataBits := stSliceConstDataBits lenTag
  if payload.size + 1 > dataBits then
    throw s!"payload too large for lenTag={lenTag}: payload={payload.size} bits, max={dataBits - 1}"
  pure (payload ++ #[true] ++ Array.replicate (dataBits - payload.size - 1) false)

private def mkStSliceConstCodeFromRaw
    (argsRefs : Nat)
    (lenTag : Nat)
    (raw : BitString)
    (refs : Array Cell) : Except String Cell := do
  if argsRefs > 3 then
    throw s!"argsRefs out of range: {argsRefs}"
  if lenTag > 7 then
    throw s!"lenTag out of range: {lenTag}"
  let args5 : Nat := (argsRefs <<< 3) + lenTag
  let word14 : Nat := (stSliceConstPrefix9 <<< 5) + args5
  pure (Cell.mkOrdinary (natToBits word14 14 ++ raw) refs)

private def mkStSliceConstInstrCode
    (payload : BitString)
    (refs : Array Cell)
    (lenTag : Nat) : Except String (Instr × Cell) := do
  if refs.size > 3 then
    throw s!"too many payload refs: {refs.size}"
  let raw ← encodeRawWithMarker payload lenTag
  let code ← mkStSliceConstCodeFromRaw refs.size lenTag raw refs
  let instr : Instr := .stSliceConst (Slice.ofCell (Cell.mkOrdinary payload refs))
  pure (instr, code)

private def mkCodeWithPreludeTail
    (prelude : Array Instr)
    (payload : BitString)
    (refs : Array Cell)
    (lenTag : Nat)
    (tail : Array Instr := #[]) : Except String (Instr × Cell) := do
  let (instr, core) ← mkStSliceConstInstrCode payload refs lenTag
  let preCell ← assembleCode prelude
  let tailCell ← assembleCode tail
  let x ← appendCodeCell preCell core
  let y ← appendCodeCell x tailCell
  pure (instr, y)

private def mkTruncatedDataCode (lenTag : Nat) : Except String Cell := do
  let raw ← encodeRawWithMarker #[true] lenTag
  let truncated := raw.take (raw.size - 1)
  mkStSliceConstCodeFromRaw 0 lenTag truncated #[]

private def mkMissingRefsCode (lenTag : Nat) (argsRefs : Nat) : Except String Cell := do
  if argsRefs = 0 then
    throw "argsRefs must be >= 1 for missing-refs shape"
  let raw ← encodeRawWithMarker #[false] lenTag
  let actualRefs : Array Cell := Array.replicate (argsRefs - 1) Cell.empty
  mkStSliceConstCodeFromRaw argsRefs lenTag raw actualRefs

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  Id.run do
    let mut out : Array Instr := #[]
    let mut rem := bits
    while rem > 0 do
      let chunk : Nat := Nat.min 256 rem
      out := out ++ #[.pushInt x, .xchg0 1, .stu chunk]
      rem := rem - chunk
    return out

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBuilderPrelude (bits : Nat) (refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkStSliceConstInstr (payload : BitString) (refs : Array Cell := #[]) : Instr :=
  .stSliceConst (Slice.ofCell (Cell.mkOrdinary payload refs))

private def runStSliceConstDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSliceConst instr stack

private def runStSliceConstDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSliceConst .add (VM.push (intV 613)) stack

private def expectedStoredBuilder (b : Builder) (payload : BitString) (refs : Array Cell) : Builder :=
  { bits := b.bits ++ payload
    refs := b.refs ++ refs }

private structure RawOracleCase where
  name : String
  code : Cell
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

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

private def mkRawCase
    (name : String)
    (initStack : Array Value)
    (prelude : Array Instr)
    (payload : BitString)
    (refs : Array Cell)
    (lenTag : Nat)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : Except String RawOracleCase := do
  let (_, code) ← mkCodeWithPreludeTail prelude payload refs lenTag tail
  pure { name, code, initStack, fuel }

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

private def randBitString (n : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:n] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def pickPayloadLen (lenTag : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxPayload : Nat := stSliceConstDataBits lenTag - 1
  let (mode, rng1) := randNat rng0 0 5
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (Nat.min 1 maxPayload, rng1)
  else if mode = 2 then
    (maxPayload, rng1)
  else if mode = 3 then
    (if maxPayload > 0 then maxPayload - 1 else 0, rng1)
  else
    randNat rng1 0 maxPayload

private def fuzzRefPool : Array Cell :=
  #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2, Cell.ofUInt 3 5]

private def genRefs (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut out : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (idx, rng') := randNat rng 0 (fuzzRefPool.size - 1)
    out := out.push (fuzzRefPool[idx]!)
    rng := rng'
  return (out, rng)

private def pickOracleNoise (rng0 : StdGen) : Value × StdGen :=
  let (tag, rng1) := randNat rng0 0 3
  if tag = 0 then
    (.null, rng1)
  else if tag = 1 then
    let (n, rng2) := randNat rng1 0 31
    (intV (Int.ofNat n - 16), rng2)
  else if tag = 2 then
    (.cell Cell.empty, rng1)
  else
    (.slice (Slice.ofCell (Cell.ofUInt 5 17)), rng1)

private def genFuzzRawCase (idx : Nat) (rng0 : StdGen) : IO (RawOracleCase × StdGen) := do
  let (shape, rng1) := randNat rng0 0 13
  let (lenTag, rng2) := randNat rng1 0 7
  let (payloadLen, rng3) := pickPayloadLen lenTag rng2
  let (payload, rng4) := randBitString payloadLen rng3
  let (refCount, rng5) := randNat rng4 0 3
  let (refs, rng6) := genRefs refCount rng5
  if shape = 0 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape0"
      (mkRawCase s!"fuzz/{idx}/ok/top-empty-builder" #[.builder Builder.empty] #[] payload refs lenTag)
    pure (c, rng6)
  else if shape = 1 then
    let (noise, rng7) := pickOracleNoise rng6
    let c ← fromExceptIO s!"fuzz/{idx}/shape1"
      (mkRawCase s!"fuzz/{idx}/ok/deep-stack-noise" #[noise, .builder Builder.empty] #[] payload refs lenTag)
    pure (c, rng7)
  else if shape = 2 then
    let maxBits := 1023 - payload.size
    let maxRefs := 4 - refs.size
    let (bBits, rng7) := randNat rng6 0 (Nat.min 63 maxBits)
    let (bRefs, rng8) := randNat rng7 0 maxRefs
    let c ← fromExceptIO s!"fuzz/{idx}/shape2"
      (mkRawCase s!"fuzz/{idx}/ok/prelude/bits-{bBits}-refs-{bRefs}" #[] (mkBuilderPrelude bBits bRefs) payload refs lenTag)
    pure (c, rng8)
  else if shape = 3 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape3"
      (mkRawCase s!"fuzz/{idx}/ok/boundary/bits1022-plus1" #[] (mkBuilderPrelude 1022 0) #[true] #[] 0)
    pure (c, rng6)
  else if shape = 4 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape4"
      (mkRawCase s!"fuzz/{idx}/ok/boundary/refs3-plus1" #[] (mkBuilderPrelude 0 3) #[] #[Cell.empty] 0)
    pure (c, rng6)
  else if shape = 5 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape5"
      (mkRawCase s!"fuzz/{idx}/underflow/empty" #[] #[] #[true] #[] 0)
    pure (c, rng6)
  else if shape = 6 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape6"
      (mkRawCase s!"fuzz/{idx}/type/top-null" #[.null] #[] #[true] #[] 0)
    pure (c, rng6)
  else if shape = 7 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape7"
      (mkRawCase s!"fuzz/{idx}/type/top-int" #[intV 9] #[] #[true] #[] 0)
    pure (c, rng6)
  else if shape = 8 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape8"
      (mkRawCase s!"fuzz/{idx}/cellov/bits-full" #[] (mkBuilderPrelude 1023 0) #[true] #[] 0)
    pure (c, rng6)
  else if shape = 9 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape9"
      (mkRawCase s!"fuzz/{idx}/cellov/refs-full" #[] (mkBuilderPrelude 0 4) #[] #[Cell.empty] 0)
    pure (c, rng6)
  else if shape = 10 then
    let c ← fromExceptIO s!"fuzz/{idx}/shape10"
      (mkRawCase s!"fuzz/{idx}/ok/prelude-mid-bits-refs" #[] (mkBuilderPrelude 31 1) (natToBits 93 7) #[Cell.empty] 1)
    pure (c, rng6)
  else if shape = 11 then
    let (noise, rng7) := pickOracleNoise rng6
    let c ← fromExceptIO s!"fuzz/{idx}/shape11"
      (mkRawCase s!"fuzz/{idx}/ok/deep-stack-noise-variant" #[noise, .builder Builder.empty] #[] (natToBits 9 4) #[] 1)
    pure (c, rng7)
  else if shape = 12 then
    let bBits := 1023 - payload.size
    let bRefs := 4 - refs.size
    let c ← fromExceptIO s!"fuzz/{idx}/shape12"
      (mkRawCase s!"fuzz/{idx}/ok/max-fit/bits-{bBits}-refs-{bRefs}" #[] (mkBuilderPrelude bBits bRefs) payload refs lenTag)
    pure (c, rng6)
  else
    let c ← fromExceptIO s!"fuzz/{idx}/shape13"
      (mkRawCase s!"fuzz/{idx}/cellov/bits-and-refs-full" #[] (mkBuilderPrelude 1023 4) #[true] #[Cell.empty] 0)
    pure (c, rng6)

private def handcraftedOracleCases : IO (Array RawOracleCase) := do
  let refA : Cell := Cell.empty
  let refB : Cell := Cell.ofUInt 1 1
  let refC : Cell := Cell.ofUInt 2 2
  let refD : Cell := Cell.ofUInt 3 5
  let payloadTrailing : BitString := #[true, false, false, true, false, false]
  let payloadLarge : BitString := Array.replicate 57 true
  let mut cases : Array RawOracleCase := #[]

  cases := cases.push (← fromExceptIO "oracle/01"
    (mkRawCase "oracle/ok/empty-builder-empty-const" #[.builder Builder.empty] #[] #[] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/02"
    (mkRawCase "oracle/ok/empty-builder-bit1" #[.builder Builder.empty] #[] #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/03"
    (mkRawCase "oracle/ok/empty-builder-trailing-zeros-preserved" #[.builder Builder.empty] #[] payloadTrailing #[] 1))
  cases := cases.push (← fromExceptIO "oracle/04"
    (mkRawCase "oracle/ok/empty-builder-with-ref1" #[.builder Builder.empty] #[] #[true, false] #[refA] 1))
  cases := cases.push (← fromExceptIO "oracle/05"
    (mkRawCase "oracle/ok/empty-builder-max-len7-ref3" #[.builder Builder.empty] #[] payloadLarge #[refA, refB, refC] 7))
  cases := cases.push (← fromExceptIO "oracle/06"
    (mkRawCase "oracle/ok/prelude-bits3-store5" #[] (mkBuilderPrelude 3 0) (natToBits 21 5) #[] 1))
  cases := cases.push (← fromExceptIO "oracle/07"
    (mkRawCase "oracle/ok/prelude-refs2-plus-ref1" #[] (mkBuilderPrelude 0 2) #[] #[refD] 0))
  cases := cases.push (← fromExceptIO "oracle/08"
    (mkRawCase "oracle/ok/prelude-bits8-refs1-plus-bits7-refs2" #[] (mkBuilderPrelude 8 1) (natToBits 73 7) #[refA, refB] 1))
  cases := cases.push (← fromExceptIO "oracle/09"
    (mkRawCase "oracle/ok/boundary-bits1022-plus1" #[] (mkBuilderPrelude 1022 0) #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/10"
    (mkRawCase "oracle/ok/boundary-refs3-plus1" #[] (mkBuilderPrelude 0 3) #[] #[refC] 0))
  cases := cases.push (← fromExceptIO "oracle/11"
    (mkRawCase "oracle/ok/deep-stack-noise-int" #[intV 11, .builder Builder.empty] #[] (natToBits 5 3) #[] 1))
  cases := cases.push (← fromExceptIO "oracle/12"
    (mkRawCase "oracle/ok/deep-stack-noise-cell-prelude" #[.cell refD] (mkBuilderPrelude 2 1) (natToBits 3 2) #[refA] 1))
  cases := cases.push (← fromExceptIO "oracle/13"
    (mkRawCase "oracle/ok/max-fit-bits-and-refs" #[] (mkBuilderPrelude (1023 - payloadLarge.size) 1) payloadLarge #[refA, refB, refC] 7))

  cases := cases.push (← fromExceptIO "oracle/14"
    (mkRawCase "oracle/underflow/empty-stack" #[] #[] #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/15"
    (mkRawCase "oracle/type/top-null" #[.null] #[] #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/16"
    (mkRawCase "oracle/type/top-int" #[intV 17] #[] #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/17"
    (mkRawCase "oracle/type/prelude-full-builder-then-null" #[] (mkBuilderPrelude 1023 0 ++ #[.pushNull]) #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/18"
    (mkRawCase "oracle/cellov/bits-full" #[] (mkBuilderPrelude 1023 0) #[true] #[] 0))
  cases := cases.push (← fromExceptIO "oracle/19"
    (mkRawCase "oracle/cellov/refs-full" #[] (mkBuilderPrelude 0 4) #[] #[refA] 0))
  cases := cases.push (← fromExceptIO "oracle/20"
    (mkRawCase "oracle/cellov/bits-and-refs-full" #[] (mkBuilderPrelude 1023 4) #[true] #[refA] 0))

  cases := cases.push (← fromExceptIO "oracle/21"
    (mkRawCase "oracle/ok/prelude-mid-bits-refs" #[] (mkBuilderPrelude 31 1) (natToBits 93 7) #[refA] 1))
  cases := cases.push (← fromExceptIO "oracle/22"
    (mkRawCase "oracle/ok/deep-stack-noise-slice" #[.slice (Slice.ofCell refB), .builder Builder.empty] #[] (natToBits 6 3) #[] 1))
  cases := cases.push (← fromExceptIO "oracle/23"
    (mkRawCase "oracle/ok/prelude-ref1-plus-const-ref3" #[] (mkBuilderPrelude 0 1) #[] #[refA, refB, refC] 0))
  cases := cases.push (← fromExceptIO "oracle/24"
    (mkRawCase "oracle/ok/boundary-bits1022-plus1-alt" #[] (mkBuilderPrelude 1022 0) #[false] #[] 0))

  pure cases

def suite : InstrSuite where
  id := stSliceConstId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let payload1 : BitString := #[true]
        let instr1 := mkStSliceConstInstr payload1
        let expected1 := expectedStoredBuilder Builder.empty payload1 #[]
        expectOkStack "ok/empty-builder-bit1"
          (runStSliceConstDirect instr1 #[.builder Builder.empty])
          #[.builder expected1]

        let payload2 : BitString := natToBits 11 4
        let refs2 : Array Cell := #[Cell.empty, Cell.ofUInt 2 2]
        let instr2 := mkStSliceConstInstr payload2 refs2
        let b2 : Builder :=
          { bits := natToBits 5 3
            refs := #[Cell.ofUInt 1 1] }
        let expected2 := expectedStoredBuilder b2 payload2 refs2
        expectOkStack "ok/non-empty-builder-append-bits-and-refs"
          (runStSliceConstDirect instr2 #[.builder b2])
          #[.builder expected2]

        let boundaryInstrBits := mkStSliceConstInstr #[true]
        let b1022 : Builder := Builder.empty.storeBits (Array.replicate 1022 false)
        let expected1023 := expectedStoredBuilder b1022 #[true] #[]
        expectOkStack "ok/boundary-bits-1022-plus-1"
          (runStSliceConstDirect boundaryInstrBits #[.builder b1022])
          #[.builder expected1023]

        let boundaryInstrRefs := mkStSliceConstInstr #[] #[Cell.ofUInt 3 5]
        let bRefs3 : Builder :=
          { Builder.empty with refs := #[Cell.empty, Cell.ofUInt 1 1, Cell.ofUInt 2 2] }
        let expectedRefs4 := expectedStoredBuilder bRefs3 #[] #[Cell.ofUInt 3 5]
        expectOkStack "ok/boundary-refs-3-plus-1"
          (runStSliceConstDirect boundaryInstrRefs #[.builder bRefs3])
          #[.builder expectedRefs4]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStSliceConstDirect instr1 #[.null, .builder Builder.empty])
          #[.null, .builder expected1] }
    ,
    { name := "unit/direct/underflow-type-cellov-and-order"
      run := do
        let smallInstr := mkStSliceConstInstr #[true]
        expectErr "underflow/empty"
          (runStSliceConstDirect smallInstr #[]) .stkUnd
        expectErr "type/top-null"
          (runStSliceConstDirect smallInstr #[.null]) .typeChk
        expectErr "type/top-int"
          (runStSliceConstDirect smallInstr #[intV 7]) .typeChk

        let refsInstr := mkStSliceConstInstr #[] #[Cell.empty]
        let fullRefs : Builder :=
          { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/refs-full-plus-one"
          (runStSliceConstDirect refsInstr #[.builder fullRefs]) .cellOv

        expectErr "cellov/bits-full-plus-one"
          (runStSliceConstDirect smallInstr #[.builder fullBuilder1023]) .cellOv

        let bothInstr := mkStSliceConstInstr #[true] #[Cell.empty]
        let fullBoth : Builder :=
          { fullBuilder1023 with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/bits-and-refs-full"
          (runStSliceConstDirect bothInstr #[.builder fullBoth]) .cellOv

        expectErr "error-order/type-before-cellov"
          (runStSliceConstDirect bothInstr #[.builder fullBuilder1023, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-embedded-payload-and-assembler-reject"
      run := do
        let payload : BitString := #[true, false, true, false, false]
        let refs : Array Cell := #[Cell.empty, Cell.ofUInt 2 2]
        let (instr, code) ← fromExceptIO "decode/main"
          (mkCodeWithPreludeTail #[] payload refs 1 #[.add])
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stsliceconst-main" s0 instr 14
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/end: expected exhausted slice, got bits={s2.bitsRemaining}, refs={s2.refsRemaining}"

        let zeroRawCode ← fromExceptIO "decode/zero-raw"
          (mkStSliceConstCodeFromRaw 0 0 (Array.replicate (stSliceConstDataBits 0) false) #[])
        let zeroInstr : Instr := .stSliceConst (Slice.ofCell Cell.empty)
        let zeroRest ← expectDecodeStep "decode/stsliceconst-zero-raw" (Slice.ofCell zeroRawCode) zeroInstr 14
        if zeroRest.bitsRemaining = 0 ∧ zeroRest.refsRemaining = 0 then
          pure ()
        else
          failUnit s!"decode/zero-raw-end: expected exhausted slice, got bits={zeroRest.bitsRemaining}, refs={zeroRest.refsRemaining}"

        match assembleCp0 [zeroInstr] with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"assemble/stsliceconst: expected invOpcode, got {e}"
        | .ok _ => failUnit "assemble/stsliceconst: expected invOpcode, got success" }
    ,
    { name := "unit/opcode/decode-invopcode-truncated-and-missing-refs"
      run := do
        let truncCode ← fromExceptIO "decode/truncated" (mkTruncatedDataCode 2)
        match decodeCp0WithBits (Slice.ofCell truncCode) with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"decode/truncated: expected invOpcode, got {e}"
        | .ok (instr, bits, _) =>
            failUnit s!"decode/truncated: expected failure, got {reprStr instr} ({bits} bits)"

        let missCode ← fromExceptIO "decode/missing-refs" (mkMissingRefsCode 3 2)
        match decodeCp0WithBits (Slice.ofCell missCode) with
        | .error .invOpcode => pure ()
        | .error e => failUnit s!"decode/missing-refs: expected invOpcode, got {e}"
        | .ok (instr, bits, _) =>
            failUnit s!"decode/missing-refs: expected failure, got {reprStr instr} ({bits} bits)" }
    ,
    { name := "unit/dispatch/non-stsliceconst-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStSliceConstDispatchFallback #[.null])
          #[.null, intV 613] }
    ,
    { name := "unit/gas/exact-and-minus-one"
      run := do
        let (_, code) ← fromExceptIO "gas/body"
          (mkCodeWithPreludeTail #[] (natToBits 13 4) #[Cell.empty] 1)
        let stack : Array Value := #[.builder Builder.empty]
        let baseline := runCodeVm code stack 1_000_000 1_000_000
        let baselineState ← expectExitCode "gas/baseline-success" (~~~ 0) baseline
        let exact := baselineState.gas.gasConsumed
        if exact ≤ 0 then
          failUnit s!"gas/exact: expected positive gas, got {exact}"
        else
          pure ()

        let exactRes := runCodeVm code stack exact exact
        let _ ← expectExitCode "gas/exact-success" (~~~ 0) exactRes

        let minus := exact - 1
        let minusRes := runCodeVm code stack minus minus
        let _ ← expectExitCode "gas/exact-minus-one-out-of-gas" Excno.outOfGas.toInt minusRes
        pure () }
    ,
    { name := "unit/oracle/handcrafted-24"
      run := do
        let cases ← handcraftedOracleCases
        if cases.size < 20 ∨ cases.size > 40 then
          failUnit s!"oracle/handcrafted: expected 20..40 cases, got {cases.size}"
        runRawOracleBatchCompare "oracle/handcrafted" cases }
    ,
    { name := "unit/oracle/fuzz-seeded-320"
      run := do
        let seed : Nat := 2026021016
        let count : Nat := 320
        let mut rng := mkStdGen seed
        let mut cases : Array RawOracleCase := #[]
        for i in [0:count] do
          let (c, rng') ← genFuzzRawCase i rng
          cases := cases.push c
          rng := rng'
        runRawOracleBatchCompare s!"oracle/fuzz/seed-{seed}" cases }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICECONST
