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

namespace Tests.Instr.Cell.PUSHREFCONT

/-
PUSHREFCONT branch map (Lean + oracle):
- execute (`execInstrFlowPushRefCont`): dispatch hit/miss + `registerCellLoad` unseen/seen
  branches, then unconditional push of `.cont (.ordinary (Slice.ofCell c) ...)`.
- decode (`decodeCp0WithBits`): `0x8a` match + `haveRefs 1` gate, yielding success or
  `.invOpcode`; adjacent single-byte opcodes (`0x89`, `0x8b`) are boundary-checked.
- asm (`assembleCp0`): `.pushRefCont` is intentionally rejected (`.invOpcode`), so
  oracle parity for this instruction must use handcrafted raw code cells.
-/

private def pushRefContId : InstrId := { name := "PUSHREFCONT" }

private def pushRefOpcode : Nat := 0x88
private def pushRefSliceOpcode : Nat := 0x89
private def pushRefContOpcode : Nat := 0x8a
private def pushSliceConstOpcode : Nat := 0x8b

private def dispatchSentinel : Int := 8088

private def pushRefContInstr (c : Cell) : Instr :=
  .pushRefCont c

private def mkCellFromBitsValue (bits : Nat) (x : Nat) : Cell :=
  if bits = 0 then
    Cell.empty
  else
    (Builder.empty.storeBits (natToBits x bits)).finalize

private def cellEmpty : Cell := Cell.empty
private def cell1 : Cell := mkCellFromBitsValue 1 1
private def cell3 : Cell := mkCellFromBitsValue 3 5
private def cell8 : Cell := mkCellFromBitsValue 8 0xA5
private def cell12 : Cell := mkCellFromBitsValue 12 0xA55
private def cellWithRef : Cell := Cell.mkOrdinary (natToBits 3 2) #[cell1]
private def cellWithTwoRefs : Cell := Cell.mkOrdinary (natToBits 0x15 5) #[cell1, cell3]
private def cellNested : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[cellWithRef, cell8]

private def contCellPool : Array Cell :=
  #[cellEmpty, cell1, cell3, cell8, cell12, cellWithRef, cellWithTwoRefs, cellNested]

private def expectedCont (c : Cell) : Value :=
  .cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty)

private def expectedPushRefContStack (c : Cell) (stack : Array Value) : Array Value :=
  stack.push (expectedCont c)

private def runPushRefContDirect (c : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowPushRefCont (pushRefContInstr c) stack

private def runPushRefContDispatchFallback (i : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowPushRefCont i (VM.push (intV dispatchSentinel)) stack

private def runPushRefContState
    (c : Cell)
    (stack : Array Value := #[])
    (loaded : Array (Array UInt8) := #[]) : Except Excno VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, loadedCells := loaded }
  let (res, st1) := (execInstrFlowPushRefCont (pushRefContInstr c) (pure ())).run st0
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def encodeOps8Bits (ops8 : Array Nat) : BitString :=
  ops8.foldl (fun acc op => acc ++ natToBits op 8) #[]

private def mkRawProgramCell
    (progPrefix : Array Instr := #[])
    (ops8 : Array Nat := #[pushRefContOpcode])
    (extraBits : BitString := #[])
    (tail : Array Instr := #[])
    (refs : Array Cell := #[]) : Except String Cell := do
  let prefixCell ←
    match assembleCp0 progPrefix.toList with
    | .ok c => pure c
    | .error e => throw s!"assembleCp0 failed for prefix: {reprStr e}"
  if prefixCell.refs.size ≠ 0 then
    throw s!"prefix unexpectedly assembled with {prefixCell.refs.size} refs"
  let tailCell ←
    match assembleCp0 tail.toList with
    | .ok c => pure c
    | .error e => throw s!"assembleCp0 failed for tail: {reprStr e}"
  if tailCell.refs.size ≠ 0 then
    throw s!"tail unexpectedly assembled with {tailCell.refs.size} refs"
  let bits := prefixCell.bits ++ encodeOps8Bits ops8 ++ extraBits ++ tailCell.bits
  pure (Cell.mkOrdinary bits refs)

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
  programPrefix : Array Instr := #[]
  ops8 : Array Nat := #[pushRefContOpcode]
  extraBits : BitString := #[]
  tail : Array Instr := #[]
  refs : Array Cell := #[]
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

private def runRawOracleCase (c : RawOracleCase) : IO Unit := do
  let code ←
    match mkRawProgramCell c.programPrefix c.ops8 c.extraBits c.tail c.refs with
    | .ok code => pure code
    | .error e => throw (IO.userError s!"{c.name}: {e}")
  let stackTokens ←
    match stackToOracleTokens c.initStack with
    | .ok toks => pure toks
    | .error e => throw (IO.userError s!"{c.name}: {e}")
  let leanCanon ←
    match leanCanonResult (TvmLeanOracleValidate.runLean code c.initStack c.fuel) with
    | .ok result => pure result
    | .error e => throw (IO.userError s!"{c.name}: {e}")
  let oracleOut ←
    try
      TvmLeanOracleValidate.runOracle code stackTokens
    catch e =>
      throw (IO.userError s!"{c.name}: oracle run failed: {e.toString}")
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
    let msg :=
      match cmp.mismatch? with
      | some mismatch => mismatch.message
      | none => "oracle comparison failed"
    throw (IO.userError s!"{c.name}: {msg}")

private def gasForInstrWithFallback (instr : Instr) (bitsFallback : Nat := 16) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr bitsFallback

private def pushRefContWordGas : Int :=
  gasForInstrWithFallback (pushRefContInstr cellEmpty) 8

private def setGasLimitWordGas : Int :=
  gasForInstrWithFallback (.tonEnvOp .setGasLimit)

private def setGasNeedForPushRefCont (n : Int) (pushCount : Nat) (cellGas : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + setGasLimitWordGas
    + Int.ofNat pushCount * pushRefContWordGas
    + cellGas
    + implicitRetGasPrice

private def computeRawSetGasExact (pushCount : Nat) (cellGas : Int) : Int := Id.run do
  let mut n : Int := 64
  for _ in [0:24] do
    let n' := setGasNeedForPushRefCont n pushCount cellGas
    if n' = n then
      return n
    n := n'
  return n

private def minusOne (n : Int) : Int :=
  if n > 0 then n - 1 else 0

private def gasExactSingleFresh : Int :=
  computeRawSetGasExact 1 cellLoadGasPrice

private def gasExactSingleFreshMinusOne : Int :=
  minusOne gasExactSingleFresh

private def gasExactTwoSame : Int :=
  computeRawSetGasExact 2 (cellLoadGasPrice + cellReloadGasPrice)

private def gasExactTwoSameMinusOne : Int :=
  minusOne gasExactTwoSame

private def gasExactTwoDistinct : Int :=
  computeRawSetGasExact 2 (cellLoadGasPrice + cellLoadGasPrice)

private def gasExactTwoDistinctMinusOne : Int :=
  minusOne gasExactTwoDistinct

private def setGasPrefix (n : Int) : Array Instr :=
  #[.pushInt (.num n), .tonEnvOp .setGasLimit]

private def pushRefContRawOracleCases : Array RawOracleCase :=
  #[
    { name := "oracle/ok/single/empty-cell-empty-stack"
      refs := #[cellEmpty]
      initStack := #[] },
    { name := "oracle/ok/single/bits1"
      refs := #[cell1]
      initStack := #[] },
    { name := "oracle/ok/single/with-ref"
      refs := #[cellWithRef]
      initStack := #[] },
    { name := "oracle/ok/single/with-two-refs"
      refs := #[cellWithTwoRefs]
      initStack := #[] },
    { name := "oracle/ok/single/deep-null-int"
      refs := #[cell3]
      initStack := #[.null, intV 7] },
    { name := "oracle/ok/single/deep-cell-slice"
      refs := #[cell12]
      initStack := #[.cell cell1, .slice (Slice.ofCell cellWithRef)] },
    { name := "oracle/ok/single/deep-builder-tuple-quit"
      refs := #[cellNested]
      initStack := #[.builder Builder.empty, .tuple #[], .cont (.quit 0)] },

    { name := "oracle/ok/chain/two-pushrefcont-diff"
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1, cell3]
      initStack := #[] },
    { name := "oracle/ok/chain/two-pushrefcont-same"
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cellWithRef, cellWithRef]
      initStack := #[.null] },
    { name := "oracle/ok/chain/pushref-then-pushrefcont"
      ops8 := #[pushRefOpcode, pushRefContOpcode]
      refs := #[cell3, cell8]
      initStack := #[] },
    { name := "oracle/ok/chain/pushrefslice-then-pushrefcont"
      ops8 := #[pushRefSliceOpcode, pushRefContOpcode]
      refs := #[cell3, cell8]
      initStack := #[intV (-3)] },
    { name := "oracle/ok/prefix/pushint-before"
      programPrefix := #[.pushInt (.num 5)]
      refs := #[cellWithTwoRefs]
      initStack := #[] },
    { name := "oracle/ok/tail/pushint-pushint-add-after"
      tail := #[.pushInt (.num 1), .pushInt (.num 2), .add]
      refs := #[cell1]
      initStack := #[.null] },

    { name := "oracle/error/decode/no-ref-single"
      refs := #[]
      initStack := #[] },
    { name := "oracle/error/decode/no-ref-after-pushref"
      ops8 := #[pushRefOpcode, pushRefContOpcode]
      refs := #[cell1]
      initStack := #[] },
    { name := "oracle/error/decode/no-ref-second-pushrefcont"
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1]
      initStack := #[intV 9] },
    { name := "oracle/error/decode/truncated-8b-neighbor"
      ops8 := #[pushSliceConstOpcode]
      refs := #[]
      initStack := #[] },
    { name := "oracle/error/decode/truncated-8b-after-pushrefcont"
      ops8 := #[pushRefContOpcode, pushSliceConstOpcode]
      refs := #[cell1]
      initStack := #[] },

    { name := "oracle/gas/exact/single-fresh"
      programPrefix := setGasPrefix gasExactSingleFresh
      refs := #[cellWithRef]
      initStack := #[] },
    { name := "oracle/gas/exact-minus-one/single-fresh"
      programPrefix := setGasPrefix gasExactSingleFreshMinusOne
      refs := #[cellWithRef]
      initStack := #[] },
    { name := "oracle/gas/exact/two-same-reload"
      programPrefix := setGasPrefix gasExactTwoSame
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1, cell1]
      initStack := #[] },
    { name := "oracle/gas/exact-minus-one/two-same-reload"
      programPrefix := setGasPrefix gasExactTwoSameMinusOne
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1, cell1]
      initStack := #[] },
    { name := "oracle/gas/exact/two-distinct"
      programPrefix := setGasPrefix gasExactTwoDistinct
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1, cell3]
      initStack := #[] },
    { name := "oracle/gas/exact-minus-one/two-distinct"
      programPrefix := setGasPrefix gasExactTwoDistinctMinusOne
      ops8 := #[pushRefContOpcode, pushRefContOpcode]
      refs := #[cell1, cell3]
      initStack := #[] }
  ]

private instance : Inhabited Value := ⟨.null⟩
private instance : Inhabited Cell := ⟨cellEmpty⟩

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def fuzzNoisePool : Array Value :=
  #[
    .null,
    intV 13,
    intV (-17),
    .cell cell3,
    .slice (Slice.ofCell cellWithRef),
    .builder Builder.empty,
    .tuple #[],
    .cont (.quit 0)
  ]

private def genPushRefContFuzzInput (rng0 : StdGen) : (Cell × Array Value) × StdGen :=
  let (c, rng1) := pickFromPool contCellPool rng0
  let (shape, rng2) := randNat rng1 0 9
  if shape = 0 then
    ((c, #[]), rng2)
  else if shape = 1 then
    ((c, #[.null]), rng2)
  else if shape = 2 then
    let (n, rng3) := randNat rng2 0 1000
    ((c, #[intV (Int.ofNat n - 500)]), rng3)
  else if shape = 3 then
    ((c, #[.cell cellWithRef]), rng2)
  else if shape = 4 then
    ((c, #[.slice (Slice.ofCell cellNested)]), rng2)
  else if shape = 5 then
    ((c, #[.builder Builder.empty]), rng2)
  else if shape = 6 then
    ((c, #[.tuple #[]]), rng2)
  else if shape = 7 then
    ((c, #[.cont (.quit 0)]), rng2)
  else if shape = 8 then
    let (x, rng3) := pickFromPool fuzzNoisePool rng2
    let (y, rng4) := pickFromPool fuzzNoisePool rng3
    ((c, #[x, y]), rng4)
  else
    let (x, rng3) := pickFromPool fuzzNoisePool rng2
    let (y, rng4) := pickFromPool fuzzNoisePool rng3
    let (z, rng5) := pickFromPool fuzzNoisePool rng4
    ((c, #[x, y, z]), rng5)

private def pushRefContFuzzSeed : UInt64 := 2026021107
private def pushRefContFuzzCount : Nat := 320

def suite : InstrSuite where
  id := pushRefContId
  unit := #[
    { name := "unit/direct/stack-shape-and-cont-payload"
      run := do
        expectOkStack "ok/empty-stack"
          (runPushRefContDirect cell1 #[])
          #[expectedCont cell1]

        expectOkStack "ok/deep-stack-preserved"
          (runPushRefContDirect cellWithRef #[.null, intV 7, .builder Builder.empty])
          #[.null, intV 7, .builder Builder.empty, expectedCont cellWithRef]

        expectOkStack "ok/cell-with-refs-preserved-in-cont"
          (runPushRefContDirect cellNested #[.slice (Slice.ofCell cell3)])
          #[.slice (Slice.ofCell cell3), expectedCont cellNested] }
    ,
    { name := "unit/direct/register-cell-load-gas-and-cache"
      run := do
        let h3 := Cell.hashBytes cell3
        let h8 := Cell.hashBytes cell8

        let fresh ←
          match runPushRefContState cell3 with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"fresh-state run failed: {e}")
        if fresh.loadedCells.size = 1 ∧ fresh.loadedCells[0]! = h3 then
          pure ()
        else
          throw (IO.userError s!"fresh-state loadedCells mismatch: {reprStr fresh.loadedCells}")
        if fresh.gas.gasConsumed = cellLoadGasPrice then
          pure ()
        else
          throw (IO.userError s!"fresh-state gas mismatch: expected {cellLoadGasPrice}, got {fresh.gas.gasConsumed}")
        if fresh.stack == #[expectedCont cell3] then
          pure ()
        else
          throw (IO.userError s!"fresh-state stack mismatch: {reprStr fresh.stack}")

        let reload ←
          match runPushRefContState cell3 #[.null] #[h3] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"reload-state run failed: {e}")
        if reload.loadedCells.size = 1 ∧ reload.loadedCells[0]! = h3 then
          pure ()
        else
          throw (IO.userError s!"reload-state loadedCells mismatch: {reprStr reload.loadedCells}")
        if reload.gas.gasConsumed = cellReloadGasPrice then
          pure ()
        else
          throw (IO.userError s!"reload-state gas mismatch: expected {cellReloadGasPrice}, got {reload.gas.gasConsumed}")
        if reload.stack == #[.null, expectedCont cell3] then
          pure ()
        else
          throw (IO.userError s!"reload-state stack mismatch: {reprStr reload.stack}")

        let distinct ←
          match runPushRefContState cell8 #[] #[h3] with
          | .ok st => pure st
          | .error e => throw (IO.userError s!"distinct-state run failed: {e}")
        if distinct.loadedCells.size = 2 ∧ distinct.loadedCells[0]! = h3 ∧ distinct.loadedCells[1]! = h8 then
          pure ()
        else
          throw (IO.userError s!"distinct-state loadedCells mismatch: {reprStr distinct.loadedCells}")
        if distinct.gas.gasConsumed = cellLoadGasPrice then
          pure ()
        else
          throw (IO.userError s!"distinct-state gas mismatch: expected {cellLoadGasPrice}, got {distinct.gas.gasConsumed}") }
    ,
    { name := "unit/opcode/decode-boundary-ref-consumption-and-errors"
      run := do
        let chain : Cell :=
          Cell.mkOrdinary
            (natToBits pushRefOpcode 8 ++ natToBits pushRefSliceOpcode 8 ++ natToBits pushRefContOpcode 8)
            #[cell1, cell3, cell8]
        let s0 := Slice.ofCell chain
        let s1 ← expectDecodeStep "decode/chain/pushref" s0 (.pushRef cell1) 8
        let s2 ← expectDecodeStep "decode/chain/pushrefslice" s1 (.pushRefSlice cell3) 8
        let s3 ← expectDecodeStep "decode/chain/pushrefcont" s2 (pushRefContInstr cell8) 8
        if s3.bitsRemaining = 0 ∧ s3.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/chain/end: expected exhausted slice, got bits={s3.bitsRemaining}, refs={s3.refsRemaining}")

        let bndCell : Cell :=
          Cell.mkOrdinary
            (natToBits pushRefSliceOpcode 8 ++ natToBits pushRefContOpcode 8 ++ natToBits pushSliceConstOpcode 8 ++
             natToBits 0 4 ++ #[false, false, false, false])
            #[cell1, cell3]
        let b0 := Slice.ofCell bndCell
        let b1 ← expectDecodeStep "decode/boundary/pushrefslice" b0 (.pushRefSlice cell1) 8
        let b2 ← expectDecodeStep "decode/boundary/pushrefcont" b1 (pushRefContInstr cell3) 8
        let b3 ← expectDecodeStep "decode/boundary/pushsliceconst-empty" b2 (.pushSliceConst (Slice.ofCell Cell.empty)) 12
        if b3.bitsRemaining = 0 ∧ b3.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/boundary/end: expected exhausted slice, got bits={b3.bitsRemaining}, refs={b3.refsRemaining}")

        expectDecodeErr "decode/pushrefcont/no-ref"
          (mkSliceFromBits (natToBits pushRefContOpcode 8))
          .invOpcode

        let oneRef : Cell :=
          Cell.mkOrdinary (natToBits pushRefContOpcode 8 ++ natToBits pushRefContOpcode 8) #[cell1]
        let c0 := Slice.ofCell oneRef
        let c1 ← expectDecodeStep "decode/one-ref/first" c0 (pushRefContInstr cell1) 8
        expectDecodeErr "decode/one-ref/second-missing"
          c1
          .invOpcode

        expectDecodeErr "decode/truncated-8b-neighbor"
          (mkSliceFromBits (natToBits pushSliceConstOpcode 8))
          .invOpcode }
    ,
    { name := "unit/asm/pushrefcont-not-assemblable"
      run := do
        match assembleCp0 [pushRefContInstr cell1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/pushrefcont: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/pushrefcont: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/hit-vs-fallback"
      run := do
        expectOkStack "dispatch/hit-pushrefcont"
          (runPushRefContDispatchFallback (pushRefContInstr cell1) #[.null])
          #[.null, expectedCont cell1]

        expectOkStack "dispatch/fallback-add"
          (runPushRefContDispatchFallback .add #[intV 3])
          #[intV 3, intV dispatchSentinel]

        expectOkStack "dispatch/fallback-pushref"
          (runPushRefContDispatchFallback (.pushRef cell3) #[])
          #[intV dispatchSentinel]

        expectOkStack "dispatch/fallback-pushrefslice"
          (runPushRefContDispatchFallback (.pushRefSlice cell3) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
    ,
    { name := "unit/raw-oracle/handcrafted-24"
      run := do
        if pushRefContRawOracleCases.size < 20 ∨ pushRefContRawOracleCases.size > 40 then
          throw (IO.userError s!"raw oracle case count must be within [20,40], got {pushRefContRawOracleCases.size}")
        for c in pushRefContRawOracleCases do
          runRawOracleCase c }
    ,
    { name := "unit/fuzz/seeded-direct-320"
      run := do
        if pushRefContFuzzCount < 240 then
          throw (IO.userError s!"fuzz count must be at least 240, got {pushRefContFuzzCount}")
        let mut rng := mkStdGen pushRefContFuzzSeed.toNat
        for i in [0:pushRefContFuzzCount] do
          let ((c, stack), rng') := genPushRefContFuzzInput rng
          rng := rng'
          let got := runPushRefContDirect c stack
          let want := expectedPushRefContStack c stack
          match got with
          | .ok out =>
              if out == want then
                pure ()
              else
                throw (IO.userError
                  s!"fuzz/direct/{i}: stack mismatch\ncell={reprStr c}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}")
          | .error e =>
              throw (IO.userError
                s!"fuzz/direct/{i}: unexpected error {e}\ncell={reprStr c}\nstack={reprStr stack}") }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHREFCONT
