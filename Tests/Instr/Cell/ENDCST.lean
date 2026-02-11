import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.ENDCST

/-
ENDCST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StbRef.lean` (`.endcst` routes to `handle true false`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcd` decodes to `.endcst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.endcst` assembles as `0xcd`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_builder_as_ref_rev`, non-quiet branch equivalent to STBREFR).

Branch map used for this suite:
- Lean ENDCST exec path: 7 branch sites / 9 terminal outcomes
  (`dispatch`; `checkUnderflow 2`; top pop as `cb2` builder/type;
   second pop as `b` builder/type; `b.canExtendBy 0 1`; success or `cellOv`).
- Decode path around opcode boundary: 3 branch sites / 4 outcomes
  (`0xcc`=`STREF`, `0xcd`=`ENDCST`, `0xce`=`STSLICE`; plus 16-bit alias `0xcf15`).
- C++ aligned path: 5 branch sites / 7 outcomes
  (`check_underflow(2)`; `pop_builder` twice (rev order); `check_space(0,1)`;
   success append finalized child as ref or throw `cell_ov`).

Key risk areas:
- reverse stack order is `... builder cb2` (cb2 on top);
- ENDCST stores `finalize(cb2)` as exactly one appended reference into `b`;
- ref-capacity-only overflow (`+0 bits`, `+1 ref`) must throw in non-quiet mode;
- ENDCST is an 8-bit opcode alias in semantics to STBREFR (`.stbRef true false`),
  but decode/assembly boundaries must remain distinct (`0xcd` vs `0xcf15`).
-/

private def endcstId : InstrId := { name := "ENDCST" }

private def endcstInstr : Instr := .endcst

private def stbrefRAliasInstr : Instr := .stbRef true false

private def dispatchSentinel : Int := 605

private def endcstOpcode : Nat := 0xcd
private def strefOpcode : Nat := 0xcc
private def stsliceOpcode : Nat := 0xce
private def stbrefRAliasOpcode : Nat := 0xcf15

private def mkEndcstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[endcstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endcstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkEndcstProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := endcstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runEndcstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef endcstInstr stack

private def runStbrefRAliasDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStbRef stbrefRAliasInstr stack

private def runEndcstDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStbRef .add (VM.push (intV dispatchSentinel)) stack

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
    throw (IO.userError
      s!"{label}: expected same outcome, lhs={reprStr lhs}, rhs={reprStr rhs}")

private def endcstSetGasExact : Int :=
  computeExactGasBudget endcstInstr

private def endcstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne endcstInstr

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  if bits = 0 then
    #[]
  else
    #[.pushInt x, .xchg0 1, .stu bits]

private def mkBuilderProgram (bits refs : Nat) (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkEndcstProgram
    (bBits bRefs cb2Bits cb2Refs : Nat)
    (bX : IntVal := .num 0)
    (cb2X : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bBits bRefs bX
    ++ mkBuilderProgram cb2Bits cb2Refs cb2X
    ++ #[endcstInstr]

private def mkEndcstProgramWithNoise
    (bBits bRefs cb2Bits cb2Refs : Nat)
    (bX : IntVal := .num 0)
    (cb2X : IntVal := .num 0) : Array Instr :=
  #[.pushNull] ++ mkEndcstProgram bBits bRefs cb2Bits cb2Refs bX cb2X

private def mkEndcstProgramTarget1023
    (cb2Bits : Nat)
    (cb2X : IntVal := .num 0) : Array Instr :=
  build1023WithFixed .stu ++ mkBuilderProgram cb2Bits 0 cb2X ++ #[endcstInstr]

private def endcstOkProgramWithRefs : Array Instr :=
  mkEndcstProgram 2 2 4 1 (.num 1) (.num 9)

private def endcstOkProgramTarget1023 : Array Instr :=
  mkEndcstProgramTarget1023 1 (.num 1)

private def endcstCellOvProgram : Array Instr :=
  mkEndcstProgram 0 4 0 0

private def endcstCellOvProgramWithBits : Array Instr :=
  mkEndcstProgram 11 4 5 1 (.num 7) (.num 19)

private def endcstBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 64, 127, 255, 256]

private def pickEndcstBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (endcstBitsBoundaryPool.size - 1)
  (endcstBitsBoundaryPool[idx]!, rng')

private def pickEndcstBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickEndcstBitsBoundary rng1
  else
    randNat rng1 0 256

private def pickEndcstRefs0To3 (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 3

private def pickEndcstRefs0To2 (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 2

private def pickEndcstNoise (rng : StdGen) : Value × StdGen :=
  let (k, rng') := randNat rng 0 2
  let v : Value :=
    if k = 0 then .null else if k = 1 then intV 77 else .cell Cell.empty
  (v, rng')

private def genEndcstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    (mkEndcstCase "fuzz/ok/init-empty-builders"
      #[.builder Builder.empty, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickEndcstNoise rng1
    (mkEndcstCase "fuzz/ok/init-deep-stack"
      #[noise, .builder Builder.empty, .builder Builder.empty], rng2)
  else if shape = 2 then
    let (bBits, rng2) := pickEndcstBitsMixed rng1
    let (cb2Bits, rng3) := pickEndcstBitsMixed rng2
    let (bRefs, rng4) := pickEndcstRefs0To3 rng3
    let (cb2Refs, rng5) := pickEndcstRefs0To2 rng4
    (mkEndcstProgramCase
      s!"fuzz/ok/program/bb-{bBits}-br-{bRefs}-cb-{cb2Bits}-cr-{cb2Refs}"
      #[]
      (mkEndcstProgram bBits bRefs cb2Bits cb2Refs),
      rng5)
  else if shape = 3 then
    let (bBits, rng2) := pickEndcstBitsMixed rng1
    let (cb2Bits, rng3) := pickEndcstBitsMixed rng2
    (mkEndcstProgramCase
      s!"fuzz/ok/program/ref-boundary/br-3-bb-{bBits}-cb-{cb2Bits}"
      #[]
      (mkEndcstProgram bBits 3 cb2Bits 1),
      rng3)
  else if shape = 4 then
    let (cb2Bits, rng2) := pickEndcstBitsMixed rng1
    (mkEndcstProgramCase
      s!"fuzz/ok/program/target-1023/cb-{cb2Bits}"
      #[]
      (mkEndcstProgramTarget1023 cb2Bits),
      rng2)
  else if shape = 5 then
    (mkEndcstCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkEndcstCase "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkEndcstCase "fuzz/type/top-not-builder" #[.builder Builder.empty, .null], rng1)
  else if shape = 8 then
    (mkEndcstCase "fuzz/type/second-not-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkEndcstCase "fuzz/type/both-non-builder" #[.null, intV 1], rng1)
  else if shape = 10 then
    let (bBits, rng2) := pickEndcstBitsMixed rng1
    let (cb2Bits, rng3) := pickEndcstBitsMixed rng2
    let (cb2Refs, rng4) := pickEndcstRefs0To2 rng3
    (mkEndcstProgramCase
      s!"fuzz/cellov/program/bb-{bBits}-br-4-cb-{cb2Bits}-cr-{cb2Refs}"
      #[]
      (mkEndcstProgram bBits 4 cb2Bits cb2Refs),
      rng4)
  else if shape = 11 then
    let (cb2Bits, rng2) := pickEndcstBitsMixed rng1
    (mkEndcstProgramCase
      s!"fuzz/cellov/program/bits-heavy/br-4-cb-{cb2Bits}"
      #[]
      (mkEndcstProgram 31 4 cb2Bits 2),
      rng2)
  else if shape = 12 then
    let (minusOne, rng2) := randBool rng1
    let budget := if minusOne then endcstSetGasExactMinusOne else endcstSetGasExact
    let tag := if minusOne then "minus-one" else "exact"
    (mkEndcstCase s!"fuzz/gas/{tag}"
      #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num budget), .tonEnvOp .setGasLimit, endcstInstr], rng2)
  else
    let (noise, rng2) := pickEndcstNoise rng1
    let (bBits, rng3) := pickEndcstBitsMixed rng2
    let (cb2Bits, rng4) := pickEndcstBitsMixed rng3
    let (bRefs, rng5) := pickEndcstRefs0To3 rng4
    let (cb2Refs, rng6) := pickEndcstRefs0To2 rng5
    (mkEndcstProgramCase
      s!"fuzz/ok/program-with-noise/bb-{bBits}-br-{bRefs}-cb-{cb2Bits}-cr-{cb2Refs}"
      #[noise]
      (mkEndcstProgram bBits bRefs cb2Bits cb2Refs),
      rng6)

def suite : InstrSuite where
  id := endcstId
  unit := #[
    { name := "unit/direct/reverse-order-success-and-preserve"
      run := do
        let child : Cell := (Builder.empty.storeBits (natToBits 3 2)).finalize
        let cb2 : Builder := { bits := natToBits 5 3, refs := #[child] }
        let b : Builder := { bits := natToBits 9 4, refs := #[Cell.empty, Cell.empty] }
        let expected : Builder := { b with refs := b.refs.push cb2.finalize }
        expectOkStack "ok/reverse-order-finalize-cb2"
          (runEndcstDirect #[.builder b, .builder cb2])
          #[.builder expected]

        expectOkStack "ok/deep-stack-preserve-below"
          (runEndcstDirect #[.null, .builder b, .builder cb2])
          #[.null, .builder expected]

        let bRef3 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty] }
        let expectedRef4 : Builder := { bRef3 with refs := bRef3.refs.push Cell.empty }
        expectOkStack "ok/ref-boundary-three-to-four"
          (runEndcstDirect #[.builder bRef3, .builder Builder.empty])
          #[.builder expectedRef4]

        let expectedBitsFull : Builder := { fullBuilder1023 with refs := #[Cell.empty] }
        expectOkStack "ok/full-bits-1023-still-accepts-ref"
          (runEndcstDirect #[.builder fullBuilder1023, .builder Builder.empty])
          #[.builder expectedBitsFull] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runEndcstDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runEndcstDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-builder" (runEndcstDirect #[.null]) .stkUnd

        expectErr "type/top-not-builder"
          (runEndcstDirect #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/second-not-builder"
          (runEndcstDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-builder"
          (runEndcstDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-ref-capacity"
      run := do
        let bRef4 : Builder := { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        let cb2Bits := Builder.empty.storeBits (natToBits 7 3)
        expectErr "cellov/target-has-four-refs-empty-cb2"
          (runEndcstDirect #[.builder bRef4, .builder Builder.empty]) .cellOv
        expectErr "cellov/target-has-four-refs-nonempty-cb2"
          (runEndcstDirect #[.builder bRef4, .builder cb2Bits]) .cellOv

        let bRef4Bits : Builder :=
          { (Builder.empty.storeBits (natToBits 31 5)) with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }
        expectErr "cellov/four-refs-even-with-target-bits"
          (runEndcstDirect #[.builder bRef4Bits, .builder Builder.empty]) .cellOv }
    ,
    { name := "unit/opcode/decode-boundaries-alias-and-assembler"
      run := do
        let endcstEncoded ←
          match assembleCp0 [endcstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/endcst failed: {e}")
        if endcstEncoded.bits = natToBits endcstOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"assemble/endcst expected 0xcd, got bits={endcstEncoded.bits}")

        let aliasEncoded ←
          match assembleCp0 [stbrefRAliasInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/stbrefR failed: {e}")
        if aliasEncoded.bits = natToBits stbrefRAliasOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/stbrefR expected 0xcf15, got bits={aliasEncoded.bits}")

        let boundaryCode : Cell :=
          Cell.mkOrdinary
            (natToBits strefOpcode 8 ++ natToBits endcstOpcode 8 ++ natToBits stsliceOpcode 8)
            #[]
        let b0 := Slice.ofCell boundaryCode
        let b1 ← expectDecodeStep "decode/boundary-cc-stref" b0 .stref 8
        let b2 ← expectDecodeStep "decode/boundary-cd-endcst" b1 endcstInstr 8
        let b3 ← expectDecodeStep "decode/boundary-ce-stslice" b2 (.stSlice false false) 8
        if b3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/boundary-end: expected bits=0, got {b3.bitsRemaining}")

        let aliasSlice := mkSliceFromBits (natToBits stbrefRAliasOpcode 16)
        let _ ← expectDecodeStep "decode/alias-cf15-to-stbrefR"
          aliasSlice stbrefRAliasInstr 16

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let mixedCode : Cell :=
          Cell.mkOrdinary
            (natToBits stbrefRAliasOpcode 16 ++ natToBits endcstOpcode 8 ++ addCell.bits)
            #[]
        let m0 := Slice.ofCell mixedCode
        let m1 ← expectDecodeStep "decode/mixed-cf15" m0 stbrefRAliasInstr 16
        let m2 ← expectDecodeStep "decode/mixed-cd" m1 endcstInstr 8
        let m3 ← expectDecodeStep "decode/mixed-tail-add" m2 .add 8
        if m3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/mixed-end: expected bits=0, got {m3.bitsRemaining}") }
    ,
    { name := "unit/alias/endcst-matches-stbrefR-semantics"
      run := do
        let stacks : Array (String × Array Value) := #[
          ("ok/minimal", #[.builder Builder.empty, .builder Builder.empty]),
          ("ok/deep-stack", #[.null, .builder Builder.empty, .builder Builder.empty]),
          ("ok/ref-boundary", #[.builder { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty] }, .builder Builder.empty]),
          ("ok/full-bits", #[.builder fullBuilder1023, .builder Builder.empty]),
          ("err/underflow-empty", #[]),
          ("err/underflow-one", #[.builder Builder.empty]),
          ("err/type-top-not-builder", #[.builder Builder.empty, .null]),
          ("err/type-second-not-builder", #[.null, .builder Builder.empty]),
          ("err/cellov-target-four-refs",
            #[.builder { Builder.empty with refs := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty] }, .builder Builder.empty])
        ]
        for (label, stack) in stacks do
          expectSameOutcome s!"alias/{label}"
            (runEndcstDirect stack)
            (runStbrefRAliasDirect stack)

        expectOkStack "dispatch/fallback"
          (runEndcstDispatchFallback #[.null])
          #[.null, intV dispatchSentinel] }
  ]
  oracle := #[
    mkEndcstCase "ok/empty-builders" #[.builder Builder.empty, .builder Builder.empty],
    mkEndcstCase "ok/deep-stack-preserve-below" #[.null, .builder Builder.empty, .builder Builder.empty],
    mkEndcstProgramCase "ok/program/b0r0-cb0r0" #[] (mkEndcstProgram 0 0 0 0),
    mkEndcstProgramCase "ok/program/b5r0-cb1r0" #[] (mkEndcstProgram 5 0 1 0 (.num 17) (.num 1)),
    mkEndcstProgramCase "ok/program/b0r1-cb3r0" #[] (mkEndcstProgram 0 1 3 0 (.num 0) (.num 5)),
    mkEndcstProgramCase "ok/program/b2r2-cb4r1" #[] endcstOkProgramWithRefs,
    mkEndcstProgramCase "ok/program/b0r3-cb7r0" #[] (mkEndcstProgram 0 3 7 0 (.num 0) (.num 33)),
    mkEndcstProgramCase "ok/program/b7r3-cb0r2" #[] (mkEndcstProgram 7 3 0 2 (.num 9) (.num 0)),
    mkEndcstProgramCase "ok/program/b31r1-cb256r0" #[] (mkEndcstProgram 31 1 256 0 (.num 1) (.num 0)),
    mkEndcstProgramCase "ok/program/b1023r0-cb1r0" #[] endcstOkProgramTarget1023,
    mkEndcstProgramCase "ok/program/noise-preserved" #[] (mkEndcstProgramWithNoise 3 1 2 1 (.num 5) (.num 3)),
    mkEndcstProgramCase "ok/program/cb2-refs-3" #[] (mkEndcstProgram 1 2 0 3 (.num 1) (.num 0)),

    mkEndcstCase "underflow/empty" #[],
    mkEndcstCase "underflow/one-item" #[.builder Builder.empty],
    mkEndcstCase "type/top-not-builder" #[.builder Builder.empty, .null],
    mkEndcstCase "type/second-not-builder" #[.null, .builder Builder.empty],
    mkEndcstCase "type/both-non-builder" #[.null, intV 1],

    mkEndcstCase "gas/exact-cost-succeeds" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num endcstSetGasExact), .tonEnvOp .setGasLimit, endcstInstr],
    mkEndcstCase "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, .builder Builder.empty]
      #[.pushInt (.num endcstSetGasExactMinusOne), .tonEnvOp .setGasLimit, endcstInstr],

    mkEndcstProgramCase "cellov/program/brefs4-cb-empty" #[] endcstCellOvProgram,
    mkEndcstProgramCase "cellov/program/brefs4-cb-bits1" #[] (mkEndcstProgram 0 4 1 0),
    mkEndcstProgramCase "cellov/program/brefs4-cb-ref1" #[] (mkEndcstProgram 0 4 0 1),
    mkEndcstProgramCase "cellov/program/brefs4-cb-bits8-ref2" #[] (mkEndcstProgram 12 4 8 2 (.num 7) (.num 13)),
    mkEndcstProgramCase "cellov/program/bits-heavy" #[] endcstCellOvProgramWithBits
  ]
  fuzz := #[
    { seed := 2026021016
      count := 500
      gen := genEndcstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.ENDCST
