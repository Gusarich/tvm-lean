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

namespace Tests.Instr.Cell.STREFCONST

/-
STREFCONST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files (mandatory):
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.stRefConst`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf20` decode with one embedded code-cell reference)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.stRefConst` / `.stRef2Const` are intentionally not assemblable; `encodeCp0` returns `invOpcode`)
- C++ analyzed file (authoritative):
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_const_ref`, `dump_store_const_ref`, `compute_len_store_const_ref`,
     opcode table registration `mkextrange(0xcf20, 0xcf22, ...)`).

Branch map used for this suite:
- Lean execute path (`execInstrCellExt`, op=`.stRefConst c`): 4 branch sites / 5 outcomes
  (`dispatch`; `checkUnderflow 1`; `popBuilder` type; `canExtendBy 0 1`; success / `cellOv`).
- Lean decode path (`0xcf20`): 3 branch sites / 3 outcomes
  (opcode match; `haveRefs 1`; decode success carrying const ref / `invOpcode`).
- C++ execute/decode path (for `STREFCONST`, i.e. refs=1) aligns:
  `have_refs(1)` in code slice, `check_underflow(1)`, `pop_builder`, `check_space(0,1)`, success.

Key risk areas:
- stack shape is builder-only (`... builder`) because cell argument is embedded in code refs;
- `cellOv` depends only on reference capacity (+0 bits, +1 ref), including 1023-bit builders;
- `0xcf20` must consume exactly one code reference and preserve remaining stream;
- assembler must reject `STREFCONST`/`STREF2CONST` (unsupported const-ref encoding in `assembleCp0`);
- gas boundary for raw code path (`PUSHINT n; SETGASLIMIT; STREFCONST`) must match oracle.
-/

private def strefConstId : InstrId := { name := "STREFCONST" }

private def strefConstOpcode : Nat := 0xcf20
private def stref2ConstOpcode : Nat := 0xcf21

private def strefConstInstr (c : Cell) : Instr :=
  .cellExt (.stRefConst c)

private def stref2ConstInstr (c1 c2 : Cell) : Instr :=
  .cellExt (.stRef2Const c1 c2)

private def dispatchSentinel : Int := Int.ofNat strefConstOpcode

private def mkCellFromBitsValue (bits : Nat) (x : Nat) : Cell :=
  if bits = 0 then
    Cell.empty
  else
    (Builder.empty.storeBits (natToBits x bits)).finalize

private def constCellEmpty : Cell := Cell.empty
private def constCell1 : Cell := mkCellFromBitsValue 1 1
private def constCell3 : Cell := mkCellFromBitsValue 3 5
private def constCell8 : Cell := mkCellFromBitsValue 8 0xA5
private def constCell15 : Cell := mkCellFromBitsValue 15 0x5AA5
private def constCellWithRef : Cell := Cell.mkOrdinary (natToBits 5 3) #[constCell1]
private def constCellWithTwoRefs : Cell := Cell.mkOrdinary (natToBits 0x1b 5) #[constCell1, constCell3]

private def constCellPool : Array Cell :=
  #[
    constCellEmpty,
    constCell1,
    constCell3,
    constCell8,
    constCell15,
    constCellWithRef,
    constCellWithTwoRefs
  ]

private def appendConstRef (b : Builder) (c : Cell) : Builder :=
  { b with refs := b.refs.push c }

private def runStrefConstDirect (c : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt (strefConstInstr c) stack

private def runStrefConstDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV dispatchSentinel)) stack

private def strefConstGasProbeInstr : Instr := strefConstInstr constCell1

private def strefConstSetGasExact : Int :=
  computeExactGasBudget strefConstGasProbeInstr

private def strefConstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne strefConstGasProbeInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def appendOneEmptyCellRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneEmptyCellRefToTopBuilder

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder refs

private def mkBuilderWithBitsRefsProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def strefConstPrefixRefs4 : Array Instr :=
  mkBuilderWithRefsProgram 4

private def strefConstPrefixRefs4Noise : Array Instr :=
  #[.pushNull] ++ strefConstPrefixRefs4

private def strefConstPrefixFullBitsRefs3 : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 3

private def strefConstPrefixFullBitsRefs4 : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder 4

private def strefConstPrefixFullBitsRefs4Noise : Array Instr :=
  #[.pushNull] ++ strefConstPrefixFullBitsRefs4

private def strefConstPrefixSetGasExact : Array Instr :=
  #[.pushInt (.num strefConstSetGasExact), .tonEnvOp .setGasLimit]

private def strefConstPrefixSetGasExactMinusOne : Array Instr :=
  #[.pushInt (.num strefConstSetGasExactMinusOne), .tonEnvOp .setGasLimit]

private def strefConstPrefixSetGasExactWithRefs3 : Array Instr :=
  mkBuilderWithRefsProgram 3 ++ strefConstPrefixSetGasExact

private def strefConstPrefixSetGasExactMinusOneWithRefs3 : Array Instr :=
  mkBuilderWithRefsProgram 3 ++ strefConstPrefixSetGasExactMinusOne

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

private def mkRawStrefConstCode (progPrefix : Array Instr) (constRef : Cell) : Except String Cell := do
  let prefixCell ←
    match assembleCp0 progPrefix.toList with
    | .ok c => pure c
    | .error e => throw s!"assembleCp0 failed for prefix: {reprStr e}"
  if prefixCell.refs.size ≠ 0 then
    throw s!"prefix unexpectedly assembled with {prefixCell.refs.size} refs"
  pure (Cell.mkOrdinary (prefixCell.bits ++ natToBits strefConstOpcode 16) #[constRef])

private structure RawOracleCase where
  name : String
  programPrefix : Array Instr := #[]
  constRef : Cell
  initStack : Array Value
  fuel : Nat := 1_000_000

private def runRawOracleCase (c : RawOracleCase) : IO Unit := do
  let code ←
    match mkRawStrefConstCode c.programPrefix c.constRef with
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

private def strefConstRawOracleCases : Array RawOracleCase :=
  #[
    -- Branch: success path (`checkUnderflow` + `popBuilder` + `canExtendBy` all pass).
    { name := "oracle/ok/direct/empty-builder-const-empty"
      constRef := constCellEmpty
      initStack := #[.builder Builder.empty] },
    { name := "oracle/ok/direct/empty-builder-const-with-ref"
      constRef := constCellWithRef
      initStack := #[.builder Builder.empty] },
    { name := "oracle/ok/direct/deep-stack-null-preserved"
      constRef := constCell1
      initStack := #[.null, .builder Builder.empty] },
    { name := "oracle/ok/direct/deep-stack-int-preserved"
      constRef := constCell8
      initStack := #[intV 77, .builder Builder.empty] },
    { name := "oracle/ok/direct/deep-stack-cell-preserved"
      constRef := constCellWithTwoRefs
      initStack := #[.cell constCell3, .builder Builder.empty] },

    -- Branch: success path on program-built builders near ref/bit boundaries.
    { name := "oracle/ok/prefix/refs0-to1"
      programPrefix := mkBuilderWithRefsProgram 0
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/ok/prefix/refs1-to2"
      programPrefix := mkBuilderWithRefsProgram 1
      constRef := constCell3
      initStack := #[] },
    { name := "oracle/ok/prefix/refs2-to3"
      programPrefix := mkBuilderWithRefsProgram 2
      constRef := constCellWithRef
      initStack := #[] },
    { name := "oracle/ok/prefix/refs3-to4"
      programPrefix := mkBuilderWithRefsProgram 3
      constRef := constCell8
      initStack := #[] },
    { name := "oracle/ok/prefix/bits7-refs1"
      programPrefix := mkBuilderWithBitsRefsProgram 7 1 (.num 85)
      constRef := constCell3
      initStack := #[] },
    { name := "oracle/ok/prefix/noise-bits3-refs2"
      programPrefix := #[.pushNull] ++ mkBuilderWithBitsRefsProgram 3 2 (.num 5)
      constRef := constCellWithRef
      initStack := #[] },
    { name := "oracle/ok/prefix/full-bits1023-refs3"
      programPrefix := strefConstPrefixFullBitsRefs3
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/ok/prefix/full-bits1023-refs0"
      programPrefix := build1023WithFixed .stu
      constRef := constCell3
      initStack := #[] },
    { name := "oracle/ok/prefix/full-bits1023-refs2-const-two-refs"
      programPrefix := build1023WithFixed .stu ++ appendRefsToTopBuilder 2
      constRef := constCellWithTwoRefs
      initStack := #[] },
    { name := "oracle/ok/prefix/const-with-two-refs"
      programPrefix := mkBuilderWithRefsProgram 2
      constRef := constCellWithTwoRefs
      initStack := #[] },

    -- Branch: `checkUnderflow` / `popBuilder` type-failure outcomes.
    { name := "oracle/underflow/empty-stack"
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/type/top-not-builder-null"
      constRef := constCell1
      initStack := #[.null] },
    { name := "oracle/type/top-not-builder-int"
      constRef := constCell1
      initStack := #[intV 9] },
    { name := "oracle/type/top-not-builder-cell"
      constRef := constCell1
      initStack := #[.cell constCell3] },
    { name := "oracle/type/top-not-builder-slice"
      constRef := constCell1
      initStack := #[.slice (Slice.ofCell constCell3)] },
    { name := "oracle/type/top-not-builder-builder-below-null"
      constRef := constCell1
      initStack := #[.builder Builder.empty, .null] },

    -- Branch: `canExtendBy 0 1` failure (`cellOv`) under ref saturation.
    { name := "oracle/cellov/prefix-refs4"
      programPrefix := strefConstPrefixRefs4
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/cellov/prefix-refs4-noise"
      programPrefix := strefConstPrefixRefs4Noise
      constRef := constCell3
      initStack := #[] },
    { name := "oracle/cellov/prefix-full-bits1023-refs4"
      programPrefix := strefConstPrefixFullBitsRefs4
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/cellov/prefix-full-bits1023-refs4-noise"
      programPrefix := strefConstPrefixFullBitsRefs4Noise
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/cellov/prefix-bits7-refs4"
      programPrefix := mkBuilderWithBitsRefsProgram 7 4 (.num 85)
      constRef := constCellWithTwoRefs
      initStack := #[] },

    -- Branch: gas edge (`setGasLimit`) around raw `STREFCONST` code path.
    { name := "oracle/gas/exact/direct-empty-builder"
      programPrefix := strefConstPrefixSetGasExact
      constRef := constCell1
      initStack := #[.builder Builder.empty] },
    { name := "oracle/gas/exact-minus-one/direct-empty-builder"
      programPrefix := strefConstPrefixSetGasExactMinusOne
      constRef := constCell1
      initStack := #[.builder Builder.empty] },
    { name := "oracle/gas/exact/prefix-refs3"
      programPrefix := strefConstPrefixSetGasExactWithRefs3
      constRef := constCell1
      initStack := #[] },
    { name := "oracle/gas/exact-minus-one/prefix-refs3"
      programPrefix := strefConstPrefixSetGasExactMinusOneWithRefs3
      constRef := constCell1
      initStack := #[] }
  ]

private def strefConstRawOracleUnitCases : Array UnitCase :=
  strefConstRawOracleCases.map fun c =>
    { name := s!"unit/raw-oracle/{c.name}"
      run := runRawOracleCase c }

private def strefConstRawOracleCaseCountMin : Nat := 30

private def strefConstRawOracleCaseCountUnit : UnitCase :=
  { name := "unit/raw-oracle/case-count-at-least-30"
    run := do
      if strefConstRawOracleUnitCases.size < strefConstRawOracleCaseCountMin then
        throw (IO.userError
          s!"raw oracle case count must be at least {strefConstRawOracleCaseCountMin}, got {strefConstRawOracleUnitCases.size}") }

private def expectedStrefConstModel (c : Cell) (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size = 0 then
    throw .stkUnd
  let top := stack.back!
  match top with
  | .builder b =>
      if !b.canExtendBy 0 1 then
        throw .cellOv
      let below := stack.extract 0 (stack.size - 1)
      pure (below.push (.builder (appendConstRef b c)))
  | _ =>
      throw .typeChk

private instance : Inhabited Builder := ⟨Builder.empty⟩

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def noisePool : Array Value :=
  #[.null, intV 41, .cell constCell1, .cell constCellWithRef]

private def okBuilderPool : Array Builder :=
  #[
    Builder.empty,
    Builder.empty.storeBits (natToBits 5 3),
    { Builder.empty with refs := #[constCell1] },
    { (Builder.empty.storeBits (natToBits 9 4)) with refs := #[constCell1, constCell3] },
    { bits := fullBuilder1023.bits, refs := #[constCell1, constCell3, constCellWithRef] }
  ]

private def ovBuilderPool : Array Builder :=
  let refs4 : Array Cell := #[constCell1, constCell3, constCellWithRef, constCell8]
  #[
    { Builder.empty with refs := refs4 },
    { bits := fullBuilder1023.bits, refs := refs4 }
  ]

private def genStrefConstDirectFuzzInput (rng0 : StdGen) : (Cell × Array Value) × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (constRef, rng2) := pickFromPool constCellPool rng1
  if shape = 0 then
    ((constRef, #[.builder Builder.empty]), rng2)
  else if shape = 1 then
    let (b, rng3) := pickFromPool okBuilderPool rng2
    ((constRef, #[.builder b]), rng3)
  else if shape = 2 then
    let (b, rng3) := pickFromPool okBuilderPool rng2
    let (noise, rng4) := pickFromPool noisePool rng3
    ((constRef, #[noise, .builder b]), rng4)
  else if shape = 3 then
    ((constRef, #[]), rng2)
  else if shape = 4 then
    ((constRef, #[.null]), rng2)
  else if shape = 5 then
    let (n, rng3) := randNat rng2 1 1000
    ((constRef, #[intV (Int.ofNat n)]), rng3)
  else if shape = 6 then
    ((constRef, #[.cell constCell3]), rng2)
  else if shape = 7 then
    let (b, rng3) := pickFromPool ovBuilderPool rng2
    ((constRef, #[.builder b]), rng3)
  else if shape = 8 then
    let (b, rng3) := pickFromPool ovBuilderPool rng2
    let (noise, rng4) := pickFromPool noisePool rng3
    ((constRef, #[noise, .builder b]), rng4)
  else if shape = 9 then
    let (noise, rng3) := pickFromPool noisePool rng2
    ((constRef, #[noise, .cell constCell1]), rng3)
  else if shape = 10 then
    let (noise1, rng3) := pickFromPool noisePool rng2
    let (noise2, rng4) := pickFromPool noisePool rng3
    ((constRef, #[noise1, noise2, .builder Builder.empty]), rng4)
  else
    let (b, rng3) := pickFromPool okBuilderPool rng2
    ((constRef, #[.null, intV 7, .builder b]), rng3)

private def strefConstFuzzSeed : UInt64 := 2026021041
private def strefConstFuzzCount : Nat := 320

def suite : InstrSuite where
  id := strefConstId
  unit := (#[
    { name := "unit/direct/success-stack-shape-and-append"
      run := do
        let expectedEmpty := appendConstRef Builder.empty constCell1
        expectOkStack "ok/minimal-empty-builder"
          (runStrefConstDirect constCell1 #[.builder Builder.empty])
          #[.builder expectedEmpty]

        let prefBuilder : Builder :=
          { bits := natToBits 6 3
            refs := #[constCell3] }
        let expectedPref := appendConstRef prefBuilder constCellWithRef
        expectOkStack "ok/preserve-bits-and-append-tail"
          (runStrefConstDirect constCellWithRef #[.builder prefBuilder])
          #[.builder expectedPref]

        let boundaryBuilder : Builder :=
          { bits := fullBuilder1023.bits
            refs := #[constCell1, constCell3, constCellWithRef] }
        let boundaryExpected := appendConstRef boundaryBuilder constCell8
        expectOkStack "ok/full-bits-with-three-refs-still-accepts-one-ref"
          (runStrefConstDirect constCell8 #[.builder boundaryBuilder])
          #[.builder boundaryExpected]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStrefConstDirect constCell3 #[.null, .builder Builder.empty])
          #[.null, .builder (appendConstRef Builder.empty constCell3)] }
    ,
    { name := "unit/direct/underflow-and-type"
      run := do
        expectErr "underflow/empty" (runStrefConstDirect constCell1 #[]) .stkUnd

        expectErr "type/top-not-builder-null"
          (runStrefConstDirect constCell1 #[.null]) .typeChk
        expectErr "type/top-not-builder-int"
          (runStrefConstDirect constCell1 #[intV 1]) .typeChk
        expectErr "type/top-not-builder-cell"
          (runStrefConstDirect constCell1 #[.cell constCell3]) .typeChk
        expectErr "type/top-not-builder-slice"
          (runStrefConstDirect constCell1 #[.slice (Slice.ofCell constCell3)]) .typeChk }
    ,
    { name := "unit/direct/cellov-ref-capacity"
      run := do
        let refs4 : Array Cell := #[constCell1, constCell3, constCellWithRef, constCell8]
        let bRef4 : Builder := { bits := #[], refs := refs4 }
        expectErr "cellov/refs4-empty-bits"
          (runStrefConstDirect constCell1 #[.builder bRef4]) .cellOv

        let bFullRef4 : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        expectErr "cellov/refs4-full-bits"
          (runStrefConstDirect constCell1 #[.builder bFullRef4]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-const-refs"
      run := do
        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")

        let d0Code : Cell :=
          Cell.mkOrdinary (natToBits strefConstOpcode 16 ++ addCell.bits) #[constCellWithRef]
        let d0 := Slice.ofCell d0Code
        let d1 ← expectDecodeStep "decode/cf20/strefconst" d0 (strefConstInstr constCellWithRef) 16
        let d2 ← expectDecodeStep "decode/cf20/tail-add" d1 .add 8
        if d2.bitsRemaining = 0 ∧ d2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/cf20/end: expected exhausted slice, got bits={d2.bitsRemaining}, refs={d2.refsRemaining}")

        let chainedCode : Cell :=
          Cell.mkOrdinary (natToBits strefConstOpcode 16 ++ natToBits strefConstOpcode 16) #[constCell1, constCell3]
        let c0 := Slice.ofCell chainedCode
        let c1 ← expectDecodeStep "decode/chained-first" c0 (strefConstInstr constCell1) 16
        let c2 ← expectDecodeStep "decode/chained-second" c1 (strefConstInstr constCell3) 16
        if c2.bitsRemaining = 0 ∧ c2.refsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/chained/end: expected exhausted slice, got bits={c2.bitsRemaining}, refs={c2.refsRemaining}")

        let twoCode : Cell :=
          Cell.mkOrdinary (natToBits stref2ConstOpcode 16) #[constCell1, constCell3]
        let _ ← expectDecodeStep "decode/cf21/stref2const" (Slice.ofCell twoCode) (stref2ConstInstr constCell1 constCell3) 16

        let missingRef := mkSliceFromBits (natToBits strefConstOpcode 16)
        match decodeCp0WithBits missingRef with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/cf20/no-ref: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/cf20/no-ref: expected failure, got success")

        let missingSecondRef : Cell := Cell.mkOrdinary (natToBits stref2ConstOpcode 16) #[constCell1]
        match decodeCp0WithBits (Slice.ofCell missingSecondRef) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/cf21/one-ref-only: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "decode/cf21/one-ref-only: expected failure, got success")

        match assembleCp0 [strefConstInstr constCell1] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/strefconst: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/strefconst: expected invOpcode, got success")

        match assembleCp0 [stref2ConstInstr constCell1 constCell3] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/stref2const: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/stref2const: expected invOpcode, got success")

        let decodedInstr ←
          match decodeCp0WithBits (Slice.ofCell d0Code) with
          | .ok (instr, _, _) => pure instr
          | .error e => throw (IO.userError s!"decode/strefconst-for-direct-exec failed: {e}")
        expectOkStack "decode+exec/const-ref-propagates"
          (runHandlerDirect execInstrCellExt decodedInstr #[.builder Builder.empty])
          #[.builder (appendConstRef Builder.empty constCellWithRef)] }
    ,
    strefConstRawOracleCaseCountUnit,
    { name := "unit/dispatch/non-strefconst-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStrefConstDispatchFallback #[.null])
          #[.null, intV dispatchSentinel] }
    ,
    { name := "unit/fuzz/seeded-direct-320"
      run := do
        if strefConstFuzzCount < 240 then
          throw (IO.userError s!"fuzz count must be at least 240, got {strefConstFuzzCount}")
        let mut rng := mkStdGen strefConstFuzzSeed.toNat
        for i in [0:strefConstFuzzCount] do
          let ((constRef, stack), rng') := genStrefConstDirectFuzzInput rng
          rng := rng'
          let got := runStrefConstDirect constRef stack
          let want := expectedStrefConstModel constRef stack
          match got, want with
          | .ok gs, .ok ws =>
              if gs == ws then
                pure ()
              else
                throw (IO.userError
                  s!"fuzz/direct/{i}: stack mismatch\nconst={reprStr constRef}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}")
          | .error ge, .error we =>
              if ge == we then
                pure ()
              else
                throw (IO.userError
                  s!"fuzz/direct/{i}: error mismatch\nconst={reprStr constRef}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}")
          | _, _ =>
              throw (IO.userError
                s!"fuzz/direct/{i}: result kind mismatch\nconst={reprStr constRef}\nstack={reprStr stack}\nwant={reprStr want}\ngot={reprStr got}") }
  ] ++ strefConstRawOracleUnitCases)
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.STREFCONST
