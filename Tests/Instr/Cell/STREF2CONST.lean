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

namespace Tests.Instr.Cell.STREF2CONST

/-
STREF2CONST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stRef2Const c1 c2)`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf21` decode + two embedded refs)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`encodeCellExtInstr` rejects embedded-ref forms with `invOpcode`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_const_ref`, `dump_store_const_ref`, opcode table `0xcf20..0xcf21`).

Branch map used for this suite:
- Lean STREF2CONST execute path: 6 branch sites / 8 terminal outcomes
  (`Instr` dispatch; `CellExt` dispatch; `checkUnderflow 1`; top pop as builder/type;
   `canExtendBy(0,2)` split; success append-two-refs or `cellOv`).
- Lean decode path for `0xcf21`: 3 branch sites / 4 terminal outcomes
  (word match; `haveRefs 2` guard; sequential `takeRefInv` preserving ref order).
- C++ aligned path (`exec_store_const_ref` with `refs=2`): 4 branch sites / 5 outcomes
  (`have_refs(2)` decode-time guard; `check_underflow(1)`; `pop_builder`; `check_space` / success).

Key risk areas:
- stack shape is `... builder` only (constants come from instruction refs, not stack);
- constants must append in code-ref order (`c1` then `c2`) and preserve builder bits/old refs;
- ref-capacity overflow is based on `+2 refs` only (bits unchanged), including full-bit builders;
- decode must require at least two embedded refs, else `invOpcode`;
- assembler currently cannot emit embedded-ref opcodes (`STREFCONST/STREF2CONST`), so
  oracle coverage for STREF2CONST is done via raw code-cell construction in unit checks.
-/

private def stref2constId : InstrId := { name := "STREF2CONST" }

private def constCell0 : Cell := Cell.empty
private def constCell1 : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
private def constCell2 : Cell := Cell.mkOrdinary (natToBits 9 4) #[Cell.empty]
private def constCell3 : Cell := Cell.mkOrdinary (natToBits 0x155 9) #[constCell1, constCell2]
private def constCell4 : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[constCell0]

private def constPool : Array Cell := #[constCell0, constCell1, constCell2, constCell3, constCell4]

private def mkStref2ConstInstr (c1 c2 : Cell) : Instr :=
  .cellExt (.stRef2Const c1 c2)

private def stref2constInstr : Instr :=
  mkStref2ConstInstr constCell1 constCell2

private def runStref2ConstDirect (c1 c2 : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt (mkStref2ConstInstr c1 c2) stack

private def runStref2ConstDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 437)) stack

private def appendConstRefs (b : Builder) (c1 c2 : Cell) : Builder :=
  { b with refs := (b.refs.push c1).push c2 }

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

private def mkBuilderWithBitsRefsProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkBuilderWithRefsProgram (refs : Nat) : Array Instr :=
  mkBuilderWithBitsRefsProgram 0 refs

private def mkBuilderFullBitsWithRefsProgram (refs : Nat) : Array Instr :=
  build1023WithFixed .stu ++ appendRefsToTopBuilder refs

private def assembleBits (program : Array Instr) : Except Excno BitString := do
  let c ← assembleCp0 program.toList
  pure c.bits

private def mkRawStref2ConstCode
    (pref : Array Instr)
    (c1 c2 : Cell)
    (suffix : Array Instr := #[]) : Except Excno Cell := do
  let preBits ← assembleBits pref
  let sufBits ← assembleBits suffix
  pure (Cell.mkOrdinary (preBits ++ natToBits 0xcf21 16 ++ sufBits) #[c1, c2])

private def mkRawCf21CodeWithRefs
    (refs : Array Cell)
    (suffix : Array Instr := #[]) : Except Excno Cell := do
  let sufBits ← assembleBits suffix
  pure (Cell.mkOrdinary (natToBits 0xcf21 16 ++ sufBits) refs)

private def liftExc {α} (label : String) (x : Except Excno α) : IO α :=
  match x with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{label}: {reprStr e}")

private def stref2constSetGasExact : Int :=
  computeExactGasBudget stref2constInstr

private def stref2constSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stref2constInstr

private structure RawOracleCase where
  name : String
  code : Cell
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

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

private def runRawOracleCase (c : RawOracleCase) : IO Unit := do
  let stackTokens ←
    match stackToOracleTokens c.initStack with
    | .ok toks => pure toks
    | .error e => throw (IO.userError s!"{c.name}: {e}")

  let leanCanon ←
    match leanCanonResult (TvmLeanOracleValidate.runLean c.code c.initStack c.fuel) with
    | .ok result => pure result
    | .error e => throw (IO.userError s!"{c.name}: {e}")

  let oracleOut ←
    try
      TvmLeanOracleValidate.runOracle c.code stackTokens
    catch e =>
      throw (IO.userError s!"{c.name}: oracle run failed: {e.toString}")

  let oracleCanon :=
    CanonResult.ofOracleRaw oracleOut.exitRaw oracleOut.gasUsed oracleOut.c4Hash oracleOut.c5Hash oracleOut.stackTop
  let cmp := compareCanonResults leanCanon oracleCanon
  if cmp.ok then
    pure ()
  else
    let msg :=
      match cmp.mismatch? with
      | some mismatch => mismatch.message
      | none => "oracle comparison failed"
    throw (IO.userError s!"{c.name}: {msg}")

private def mkRawCase
    (name : String)
    (pref : Array Instr)
    (c1 c2 : Cell)
    (initStack : Array Value := #[]
    )
    (suffix : Array Instr := #[])
    (fuel : Nat := 1_000_000) : IO RawOracleCase := do
  let code ← liftExc name (mkRawStref2ConstCode pref c1 c2 suffix)
  pure { name, code, initStack, fuel }

private def buildRawOracleCases : IO (Array RawOracleCase) := do
  let mut cases : Array RawOracleCase := #[]

  cases := cases.push (← mkRawCase "oracle/ok/direct/empty-builder"
    #[] constCell1 constCell2 #[.builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/ok/direct/deep-null"
    #[] constCell3 constCell4 #[.null, .builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/ok/direct/deep-int"
    #[] constCell0 constCell2 #[intV 5, .builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/ok/direct/swapped-consts"
    #[] constCell2 constCell1 #[.builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/ok/direct/nested-consts"
    #[] constCell3 constCell0 #[.builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/ok/direct/alt-pair"
    #[] constCell4 constCell3 #[.builder Builder.empty])

  cases := cases.push (← mkRawCase "oracle/err/underflow-empty"
    #[] constCell1 constCell2 #[])
  cases := cases.push (← mkRawCase "oracle/err/type-null"
    #[] constCell1 constCell2 #[.null])
  cases := cases.push (← mkRawCase "oracle/err/type-int"
    #[] constCell1 constCell2 #[intV 11])
  cases := cases.push (← mkRawCase "oracle/err/type-cell"
    #[] constCell1 constCell2 #[.cell constCell0])

  cases := cases.push (← mkRawCase "oracle/ok/program/refs0"
    (mkBuilderWithRefsProgram 0) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/ok/program/refs1"
    (mkBuilderWithRefsProgram 1) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/ok/program/refs2"
    (mkBuilderWithRefsProgram 2) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/ok/program/bits7-refs1"
    (mkBuilderWithBitsRefsProgram 7 1 (.num 65)) constCell3 constCell4)
  cases := cases.push (← mkRawCase "oracle/ok/program/fullbits-refs2"
    (mkBuilderFullBitsWithRefsProgram 2) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/ok/program/noise-null-refs2"
    (#[.pushNull] ++ mkBuilderWithRefsProgram 2) constCell1 constCell2)

  cases := cases.push (← mkRawCase "oracle/err/cellov-refs3"
    (mkBuilderWithRefsProgram 3) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/err/cellov-refs4"
    (mkBuilderWithRefsProgram 4) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/err/cellov-bits3-refs3"
    (mkBuilderWithBitsRefsProgram 3 3 (.num 5)) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/err/cellov-fullbits-refs3"
    (mkBuilderFullBitsWithRefsProgram 3) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/err/cellov-noise-null"
    (#[.pushNull] ++ mkBuilderWithRefsProgram 3) constCell1 constCell2)
  cases := cases.push (← mkRawCase "oracle/err/cellov-noise-int"
    (#[.pushInt (.num 42)] ++ mkBuilderWithRefsProgram 3) constCell1 constCell2)

  let oneRefCode ← liftExc "oracle/err/decode-one-ref" (mkRawCf21CodeWithRefs #[constCell1])
  cases := cases.push { name := "oracle/err/decode-one-ref", code := oneRefCode, initStack := #[.builder Builder.empty] }
  let zeroRefCode ← liftExc "oracle/err/decode-zero-ref" (mkRawCf21CodeWithRefs #[])
  cases := cases.push { name := "oracle/err/decode-zero-ref", code := zeroRefCode, initStack := #[.builder Builder.empty] }

  cases := cases.push (← mkRawCase "oracle/gas/exact"
    #[.pushInt (.num stref2constSetGasExact), .tonEnvOp .setGasLimit]
    constCell1 constCell2 #[.builder Builder.empty])
  cases := cases.push (← mkRawCase "oracle/gas/exact-minus-one"
    #[.pushInt (.num stref2constSetGasExactMinusOne), .tonEnvOp .setGasLimit]
    constCell1 constCell2 #[.builder Builder.empty])

  pure cases

private def pickCellFromPool (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (constPool.size - 1)
  (constPool[idx]!, rng')

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 91
    else if pick = 2 then .cell constCell2
    else intV (-7)
  (v, rng1)

private def pickRefs (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (c, rng') := pickCellFromPool rng
    refs := refs.push c
    rng := rng'
  return (refs, rng)

private def pickSmallBits (rng0 : StdGen) : BitString × StdGen :=
  let (bits, rng1) := randNat rng0 0 16
  if bits = 0 then
    (#[], rng1)
  else
    let maxVal : Nat := (1 <<< bits) - 1
    let (x, rng2) := randNat rng1 0 maxVal
    (natToBits x bits, rng2)

private def runStructuredFuzzIter (iter : Nat) (rng0 : StdGen) : IO StdGen := do
  let (c1, rng1) := pickCellFromPool rng0
  let (c2, rng2) := pickCellFromPool rng1
  let (shape, rng3) := randNat rng2 0 11

  if shape = 0 then
    let expected := appendConstRefs Builder.empty c1 c2
    expectOkStack s!"fuzz/{iter}/ok/top-only"
      (runStref2ConstDirect c1 c2 #[.builder Builder.empty])
      #[.builder expected]
    pure rng3
  else if shape = 1 then
    let (noise, rng4) := pickNoiseValue rng3
    let expected := appendConstRefs Builder.empty c1 c2
    expectOkStack s!"fuzz/{iter}/ok/deep-stack"
      (runStref2ConstDirect c1 c2 #[noise, .builder Builder.empty])
      #[noise, .builder expected]
    pure rng4
  else if shape = 2 then
    let (refsN, rng4) := randNat rng3 0 2
    let (refs, rng5) := pickRefs refsN rng4
    let (bits, rng6) := pickSmallBits rng5
    let b : Builder := { bits := bits, refs := refs }
    let expected := appendConstRefs b c1 c2
    expectOkStack s!"fuzz/{iter}/ok/random-bits-refs{refsN}"
      (runStref2ConstDirect c1 c2 #[.builder b])
      #[.builder expected]
    pure rng6
  else if shape = 3 then
    let (refs, rng4) := pickRefs 2 rng3
    let b : Builder := { bits := fullBuilder1023.bits, refs := refs }
    let expected := appendConstRefs b c1 c2
    expectOkStack s!"fuzz/{iter}/ok/fullbits-refs2"
      (runStref2ConstDirect c1 c2 #[.builder b])
      #[.builder expected]
    pure rng4
  else if shape = 4 then
    let (refs, rng4) := pickRefs 3 rng3
    let (bits, rng5) := pickSmallBits rng4
    let b : Builder := { bits := bits, refs := refs }
    expectErr s!"fuzz/{iter}/cellov/refs3"
      (runStref2ConstDirect c1 c2 #[.builder b]) .cellOv
    pure rng5
  else if shape = 5 then
    let (refs, rng4) := pickRefs 4 rng3
    let b : Builder := { bits := fullBuilder1023.bits, refs := refs }
    expectErr s!"fuzz/{iter}/cellov/refs4"
      (runStref2ConstDirect c1 c2 #[.builder b]) .cellOv
    pure rng4
  else if shape = 6 then
    expectErr s!"fuzz/{iter}/underflow/empty"
      (runStref2ConstDirect c1 c2 #[]) .stkUnd
    pure rng3
  else if shape = 7 then
    expectErr s!"fuzz/{iter}/type/top-null"
      (runStref2ConstDirect c1 c2 #[.null]) .typeChk
    pure rng3
  else if shape = 8 then
    expectErr s!"fuzz/{iter}/type/top-int-builder-below"
      (runStref2ConstDirect c1 c2 #[.builder Builder.empty, intV 3]) .typeChk
    pure rng3
  else if shape = 9 then
    expectErr s!"fuzz/{iter}/type/top-cell"
      (runStref2ConstDirect c1 c2 #[intV 7, .cell c1]) .typeChk
    pure rng3
  else if shape = 10 then
    let (noise, rng4) := pickNoiseValue rng3
    expectOkStack s!"fuzz/{iter}/dispatch/fallback"
      (runStref2ConstDispatchFallback #[noise])
      #[noise, intV 437]
    pure rng4
  else
    let (noise, rng4) := pickNoiseValue rng3
    let (refs, rng5) := pickRefs 1 rng4
    let b : Builder := { bits := #[], refs := refs }
    let expected := appendConstRefs b c1 c2
    expectOkStack s!"fuzz/{iter}/ok/deep-random-builder"
      (runStref2ConstDirect c1 c2 #[noise, .builder b])
      #[noise, .builder expected]
    pure rng5

def suite : InstrSuite where
  id := stref2constId
  unit := #[
    { name := "unit/direct/success-stack-order-and-append"
      run := do
        let expected0 := appendConstRefs Builder.empty constCell1 constCell2
        expectOkStack "ok/store-empty-builder"
          (runStref2ConstDirect constCell1 constCell2 #[.builder Builder.empty])
          #[.builder expected0]

        let prefBuilder : Builder := { bits := natToBits 6 3, refs := #[constCell0] }
        let expectedPref := appendConstRefs prefBuilder constCell3 constCell4
        expectOkStack "ok/append-tail-preserve-bits-and-old-refs"
          (runStref2ConstDirect constCell3 constCell4 #[.builder prefBuilder])
          #[.builder expectedPref]

        let boundaryBuilder : Builder := { bits := fullBuilder1023.bits, refs := #[constCell0, constCell1] }
        let boundaryExpected := appendConstRefs boundaryBuilder constCell1 constCell2
        expectOkStack "ok/full-bits-refs2-to-refs4"
          (runStref2ConstDirect constCell1 constCell2 #[.builder boundaryBuilder])
          #[.builder boundaryExpected]

        let deepExpected := appendConstRefs Builder.empty constCell2 constCell1
        expectOkStack "ok/deep-stack-preserve-below"
          (runStref2ConstDirect constCell2 constCell1 #[intV 77, .null, .builder Builder.empty])
          #[intV 77, .null, .builder deepExpected] }
    ,
    { name := "unit/direct/underflow-type-and-cellov"
      run := do
        expectErr "underflow/empty"
          (runStref2ConstDirect constCell1 constCell2 #[]) .stkUnd

        expectErr "type/top-null"
          (runStref2ConstDirect constCell1 constCell2 #[.null]) .typeChk
        expectErr "type/top-cell"
          (runStref2ConstDirect constCell1 constCell2 #[.cell constCell0]) .typeChk
        expectErr "type/top-int-builder-below"
          (runStref2ConstDirect constCell1 constCell2 #[.builder Builder.empty, intV 9]) .typeChk
        expectErr "type/top-int"
          (runStref2ConstDirect constCell1 constCell2 #[intV (-1)]) .typeChk

        let refs3Builder : Builder := { bits := #[], refs := #[constCell0, constCell1, constCell2] }
        expectErr "cellov/refs3"
          (runStref2ConstDirect constCell1 constCell2 #[.builder refs3Builder]) .cellOv

        let refs4Builder : Builder := { bits := #[], refs := #[constCell0, constCell1, constCell2, constCell3] }
        expectErr "cellov/refs4"
          (runStref2ConstDirect constCell1 constCell2 #[.builder refs4Builder]) .cellOv

        let fullRefs3Builder : Builder := { bits := fullBuilder1023.bits, refs := #[constCell0, constCell1, constCell2] }
        expectErr "cellov/full-bits-refs3"
          (runStref2ConstDirect constCell1 constCell2 #[.builder fullRefs3Builder]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-embedded-refs"
      run := do
        let addBits ← liftExc "assemble/add-bits" (assembleBits #[.add])
        let code : Cell := Cell.mkOrdinary (natToBits 0xcf21 16 ++ addBits) #[constCell1, constCell2, constCell3]

        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stref2const-cf21" s0 (mkStref2ConstInstr constCell1 constCell2) 16
        if s1.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError s!"decode/stref2const-cf21: expected refsRemaining=1, got {s1.refsRemaining}")

        let s2 ← expectDecodeStep "decode/stref2const-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 ∧ s2.refsRemaining = 1 then
          pure ()
        else
          throw (IO.userError s!"decode/stref2const-tail-end: expected bits=0 refs=1, got bits={s2.bitsRemaining} refs={s2.refsRemaining}")

        let badOneRef : Cell := Cell.mkOrdinary (natToBits 0xcf21 16) #[constCell1]
        match decodeCp0WithBits (Slice.ofCell badOneRef) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/cf21-one-ref: expected invOpcode, got {e}")
        | .ok (i, b, _) => throw (IO.userError s!"decode/cf21-one-ref: expected failure, got instr={reprStr i} bits={b}")

        let badZeroRef : Cell := Cell.mkOrdinary (natToBits 0xcf21 16) #[]
        match decodeCp0WithBits (Slice.ofCell badZeroRef) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode/cf21-zero-ref: expected invOpcode, got {e}")
        | .ok (i, b, _) => throw (IO.userError s!"decode/cf21-zero-ref: expected failure, got instr={reprStr i} bits={b}")

        match assembleCp0 [mkStref2ConstInstr constCell1 constCell2] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"assemble/stref2const: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "assemble/stref2const: expected invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStref2ConstDispatchFallback #[.null])
          #[.null, intV 437] }
    ,
    { name := "unit/oracle/raw-crosscheck-handcrafted-26"
      run := do
        let cases ← buildRawOracleCases
        if !(20 ≤ cases.size ∧ cases.size ≤ 40) then
          throw (IO.userError s!"oracle/cases: expected 20..40 cases, got {cases.size}")
        for c in cases do
          runRawOracleCase c }
    ,
    { name := "unit/fuzz/structured-seeded-320"
      run := do
        let mut rng := mkStdGen 2026021027
        for i in [0:320] do
          rng := (← runStructuredFuzzIter i rng) }
  ]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.STREF2CONST
