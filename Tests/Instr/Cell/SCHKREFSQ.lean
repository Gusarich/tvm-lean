import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCHKREFSQ

/-
SCHKREFSQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/SchkRefs.lean` (`.schkRefs true`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SCHKREFSQ` encode: `0xd746`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd746` decode to `.cellOp (.schkRefs true)`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_chk_op_args`, opcode `0xd746`, max arg `1023`, quiet=true).

Branch map for `SCHKREFSQ`:
- underflow gate requires exactly 2 stack items;
- pop order is `refs` (top, range `0..1023`) then `slice`;
- quiet success pushes `-1`; quiet short-slice failure pushes `0`;
- refs `5..1023` are range-valid and must produce quiet status `0` (not range errors);
- non-quiet contrast (`SCHKREFS`) throws `.cellUnd` on short refs.
-/

private def schkRefsQId : InstrId := { name := "SCHKREFSQ" }

private def schkRefsInstr : Instr :=
  .cellOp (.schkRefs false)

private def schkRefsQInstr : Instr :=
  .cellOp (.schkRefs true)

private def schkBitsInstr : Instr :=
  .cellOp (.schkBits false)

private def schkBitRefsInstr : Instr :=
  .cellOp (.schkBitRefs false)

private def schkBitsQInstr : Instr :=
  .cellOp (.schkBits true)

private def schkBitRefsQInstr : Instr :=
  .cellOp (.schkBitRefs true)

private def schkBitsWord : Nat := 0xd741
private def schkRefsWord : Nat := 0xd742
private def schkBitRefsWord : Nat := 0xd743
private def schkBitsQWord : Nat := 0xd745
private def schkRefsQWord : Nat := 0xd746
private def schkBitRefsQWord : Nat := 0xd747

private def dispatchSentinel : Int := 55110

private def execCellOpSchkRefsInstr (i : Instr) (next : VM Unit) : VM Unit :=
  match i with
  | .cellOp op => execCellOpSchkRefs op next
  | _ => next

private def mkSchkRefsQCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[schkRefsQInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSchkRefsQProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := schkRefsQId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSchkRefsDirect (quiet : Bool) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execCellOpSchkRefsInstr (.cellOp (.schkRefs quiet)) stack

private def runSchkRefsQDirect (stack : Array Value) : Except Excno (Array Value) :=
  runSchkRefsDirect true stack

private def runSchkRefsQDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execCellOpSchkRefsInstr instr (VM.push (intV dispatchSentinel)) stack

private def schkRefsQSetGasExact : Int :=
  computeExactGasBudget schkRefsQInstr

private def schkRefsQSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne schkRefsQInstr

private def patternedBits (n : Nat) : BitString :=
  Array.ofFn (n := n) fun i => (i.1 % 2 = 0) || (i.1 % 5 = 3)

private def refCellA : Cell :=
  (Builder.empty.storeBits (natToBits 1 1)).finalize

private def refCellB : Cell :=
  (Builder.empty.storeBits (natToBits 2 2)).finalize

private def refCellC : Cell :=
  (Builder.empty.storeBits (natToBits 0xA5 8)).finalize

private def refCellD : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[Cell.empty]

private def mkRefCells : Nat → Array Cell
  | 0 => #[]
  | 1 => #[refCellA]
  | 2 => #[refCellA, refCellB]
  | 3 => #[refCellA, refCellB, refCellC]
  | _ => #[refCellA, refCellB, refCellC, refCellD]

private def mkSliceWithRefs (bits refs : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternedBits bits) (mkRefCells refs))

private def oracleSliceRefs0 : Slice := mkSliceWithRefs 5 0
private def oracleSliceRefs1 : Slice := mkSliceWithRefs 7 1
private def oracleSliceRefs2 : Slice := mkSliceWithRefs 9 2
private def oracleSliceRefs3 : Slice := mkSliceWithRefs 11 3
private def oracleSliceRefs4 : Slice := mkSliceWithRefs 13 4

private def partialBaseCell : Cell :=
  Cell.mkOrdinary (patternedBits 19) (mkRefCells 4)

private def partialRefsSlice : Slice :=
  { cell := partialBaseCell, bitPos := 6, refPos := 1 } -- refsRemaining = 3

private def exhaustedRefsSlice : Slice :=
  { cell := partialBaseCell, bitPos := 2, refPos := 4 } -- refsRemaining = 0

private def oracleNoiseSlice : Slice :=
  mkSliceFromBits (natToBits 0x15 5)

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkSliceProgramRefs (sliceRefs : Nat) : Array Instr :=
  #[.newc] ++ appendRefsToTopBuilder sliceRefs ++ #[.endc, .ctos]

private def mkSchkRefsQProgram (sliceRefs needRefs : Nat) : Array Instr :=
  mkSliceProgramRefs sliceRefs ++ #[.pushInt (.num (Int.ofNat needRefs)), schkRefsQInstr]

private def schkProgramRefsNan : Array Instr :=
  mkSliceProgramRefs 0 ++ #[.pushInt .nan, schkRefsQInstr]

private def sliceRefsPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickFromNatPool (rng : StdGen) (pool : Array Nat) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNeedRefsWithin (rng : StdGen) (sliceRefs : Nat) : Nat × StdGen :=
  if sliceRefs = 0 then
    (0, rng)
  else
    let (mode, rng1) := randNat rng 0 4
    if mode = 0 then
      (0, rng1)
    else if mode = 1 then
      (sliceRefs, rng1)
    else if mode = 2 then
      (sliceRefs - 1, rng1)
    else if mode = 3 then
      (Nat.min 1 sliceRefs, rng1)
    else
      randNat rng1 0 sliceRefs

private def pickNeedRefsOverflow (rng : StdGen) (sliceRefs : Nat) : Nat × StdGen :=
  let minNeed : Nat := sliceRefs + 1
  let maxNeed : Nat := 1023
  if minNeed >= maxNeed then
    (minNeed, rng)
  else
    let (mode, rng1) := randNat rng 0 3
    if mode = 0 then
      (minNeed, rng1)
    else if mode = 1 then
      (maxNeed, rng1)
    else if mode = 2 then
      (Nat.min maxNeed (minNeed + 1), rng1)
    else
      randNat rng1 minNeed maxNeed

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell refCellA
    else if pick = 3 then .slice oracleNoiseSlice
    else .slice oracleSliceRefs1
  (noise, rng1)

private def genSchkRefsQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let (sliceRefs, rng2) := pickFromNatPool rng1 sliceRefsPool
    let (needRefs, rng3) := pickNeedRefsWithin rng2 sliceRefs
    (mkSchkRefsQCase s!"fuzz/ok/direct/refs{sliceRefs}/need{needRefs}"
      #[.slice (mkSliceWithRefs 10 sliceRefs), intV (Int.ofNat needRefs)], rng3)
  else if shape = 1 then
    let (sliceRefs, rng2) := pickFromNatPool rng1 sliceRefsPool
    let (needRefs, rng3) := pickNeedRefsWithin rng2 sliceRefs
    let (noise, rng4) := pickNoiseValue rng3
    (mkSchkRefsQCase s!"fuzz/ok/direct/noise/refs{sliceRefs}/need{needRefs}"
      #[noise, .slice (mkSliceWithRefs 10 sliceRefs), intV (Int.ofNat needRefs)], rng4)
  else if shape = 2 then
    let (sliceRefs, rng2) := pickFromNatPool rng1 sliceRefsPool
    let (needRefs, rng3) := pickNeedRefsOverflow rng2 sliceRefs
    (mkSchkRefsQCase s!"fuzz/fail/direct/refs{sliceRefs}/need{needRefs}"
      #[.slice (mkSliceWithRefs 10 sliceRefs), intV (Int.ofNat needRefs)], rng3)
  else if shape = 3 then
    let (sliceRefs, rng2) := pickFromNatPool rng1 sliceRefsPool
    let (noise, rng3) := pickNoiseValue rng2
    (mkSchkRefsQCase s!"fuzz/fail/direct/max/refs{sliceRefs}"
      #[noise, .slice (mkSliceWithRefs 12 sliceRefs), intV 1023], rng3)
  else if shape = 4 then
    (mkSchkRefsQCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkSchkRefsQCase "fuzz/underflow/one-item" #[.slice oracleSliceRefs2], rng1)
  else if shape = 6 then
    (mkSchkRefsQCase "fuzz/type/refs-top-not-int" #[.slice oracleSliceRefs2, .null], rng1)
  else if shape = 7 then
    (mkSchkRefsQCase "fuzz/range/refs-negative" #[.slice oracleSliceRefs2, intV (-1)], rng1)
  else if shape = 8 then
    (mkSchkRefsQCase "fuzz/range/refs-gt1023" #[.slice oracleSliceRefs2, intV 1024], rng1)
  else if shape = 9 then
    (mkSchkRefsQCase "fuzz/type/slice-not-slice" #[.null, intV 0], rng1)
  else if shape = 10 then
    (mkSchkRefsQCase "fuzz/order/refs-range-before-slice-type" #[.null, intV 1024], rng1)
  else if shape = 11 then
    (mkSchkRefsQCase "fuzz/order/refs-type-before-slice-type" #[.null, .null], rng1)
  else if shape = 12 then
    (mkSchkRefsQProgramCase "fuzz/range/program-refs-nan" #[] schkProgramRefsNan, rng1)
  else if shape = 13 then
    let (sliceRefs, rng2) := pickFromNatPool rng1 sliceRefsPool
    let (mode, rng3) := randNat rng2 0 1
    if mode = 0 then
      let (needRefs, rng4) := pickNeedRefsWithin rng3 sliceRefs
      (mkSchkRefsQProgramCase
        s!"fuzz/program/ok/srefs{sliceRefs}/need{needRefs}"
        #[]
        (mkSchkRefsQProgram sliceRefs needRefs), rng4)
    else
      let (needRefs, rng4) := pickNeedRefsOverflow rng3 sliceRefs
      let (noise, rng5) := pickNoiseValue rng4
      (mkSchkRefsQProgramCase
        s!"fuzz/program/fail/srefs{sliceRefs}/need{needRefs}"
        #[noise]
        (mkSchkRefsQProgram sliceRefs needRefs), rng5)
  else if shape = 14 then
    (mkSchkRefsQCase "fuzz/gas/exact"
      #[.slice oracleSliceRefs4, intV 0]
      #[.pushInt (.num schkRefsQSetGasExact), .tonEnvOp .setGasLimit, schkRefsQInstr], rng1)
  else
    (mkSchkRefsQCase "fuzz/gas/exact-minus-one"
      #[.slice oracleSliceRefs4, intV 0]
      #[.pushInt (.num schkRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkRefsQInstr], rng1)

def suite : InstrSuite where
  id := { name := "SCHKREFSQ" }
  unit := #[
    { name := "unit/direct/quiet-success-status-and-stack-shape"
      run := do
        expectOkStack "ok/refs0-need0"
          (runSchkRefsQDirect #[.slice oracleSliceRefs0, intV 0])
          #[intV (-1)]
        expectOkStack "ok/refs2-need1"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, intV 1])
          #[intV (-1)]
        expectOkStack "ok/refs4-need4"
          (runSchkRefsQDirect #[.slice oracleSliceRefs4, intV 4])
          #[intV (-1)]
        expectOkStack "ok/partial-refpos1-need3"
          (runSchkRefsQDirect #[.slice partialRefsSlice, intV 3])
          #[intV (-1)]
        expectOkStack "ok/partial-exhausted-need0"
          (runSchkRefsQDirect #[.slice exhaustedRefsSlice, intV 0])
          #[intV (-1)]
        expectOkStack "ok/deep-stack-preserve-below"
          (runSchkRefsQDirect #[.null, intV 77, .slice oracleSliceRefs3, intV 2])
          #[.null, intV 77, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-status-zero"
      run := do
        expectOkStack "fail/refs0-need1"
          (runSchkRefsQDirect #[.slice oracleSliceRefs0, intV 1])
          #[intV 0]
        expectOkStack "fail/refs2-need3"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, intV 3])
          #[intV 0]
        expectOkStack "fail/refs4-need5"
          (runSchkRefsQDirect #[.slice oracleSliceRefs4, intV 5])
          #[intV 0]
        expectOkStack "fail/refs4-need1023"
          (runSchkRefsQDirect #[.slice oracleSliceRefs4, intV 1023])
          #[intV 0]
        expectOkStack "fail/partial-refpos1-need4-deep-stack"
          (runSchkRefsQDirect #[.slice oracleNoiseSlice, .slice partialRefsSlice, intV 4])
          #[.slice oracleNoiseSlice, intV 0] }
    ,
    { name := "unit/direct/underflow-range-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runSchkRefsQDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2]) .stkUnd

        expectErr "type/refs-top-not-int"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, .null]) .typeChk
        expectErr "range/refs-negative"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, intV (-1)]) .rangeChk
        expectErr "range/refs-gt1023"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, intV 1024]) .rangeChk
        expectErr "range/refs-nan"
          (runSchkRefsQDirect #[.slice oracleSliceRefs2, .int .nan]) .rangeChk

        expectErr "type/slice-not-slice-after-valid-refs"
          (runSchkRefsQDirect #[.null, intV 0]) .typeChk
        expectErr "order/refs-range-before-slice-type"
          (runSchkRefsQDirect #[.null, intV 1024]) .rangeChk
        expectErr "order/refs-type-before-slice-type"
          (runSchkRefsQDirect #[.null, .null]) .typeChk }
    ,
    { name := "unit/direct/non-quiet-contrast-schkrefs"
      run := do
        expectOkStack "schkrefs/non-quiet-success-empty-result"
          (runSchkRefsDirect false #[.slice oracleSliceRefs4, intV 4])
          #[]
        expectOkStack "schkrefs/non-quiet-success-deep-stack-preserve"
          (runSchkRefsDirect false #[intV 9, .slice partialRefsSlice, intV 2])
          #[intV 9]
        expectErr "schkrefs/non-quiet-failure-need5-have4"
          (runSchkRefsDirect false #[.slice oracleSliceRefs4, intV 5]) .cellUnd
        expectErr "schkrefs/non-quiet-failure-need1023-have0"
          (runSchkRefsDirect false #[.slice oracleSliceRefs0, intV 1023]) .cellUnd }
    ,
    { name := "unit/opcode/decode-assembler-boundaries"
      run := do
        let asmProgram : Array Instr :=
          #[schkBitsInstr, schkRefsInstr, schkBitRefsInstr, schkBitsQInstr, schkRefsQInstr, schkBitRefsQInstr, .add]
        let code ←
          match assembleCp0 asmProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/asm-schkbits" s0 schkBitsInstr 16
        let s2 ← expectDecodeStep "decode/asm-schkrefs" s1 schkRefsInstr 16
        let s3 ← expectDecodeStep "decode/asm-schkbitrefs" s2 schkBitRefsInstr 16
        let s4 ← expectDecodeStep "decode/asm-schkbitsq" s3 schkBitsQInstr 16
        let s5 ← expectDecodeStep "decode/asm-schkrefsq" s4 schkRefsQInstr 16
        let s6 ← expectDecodeStep "decode/asm-schkbitrefsq" s5 schkBitRefsQInstr 16
        let s7 ← expectDecodeStep "decode/asm-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let codeQ ←
          match assembleCp0 [schkRefsQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/schkrefsq failed: {e}")
        if codeQ.bits = natToBits schkRefsQWord 16 && codeQ.refs.isEmpty then
          pure ()
        else
          throw (IO.userError s!"assemble/schkrefsq: expected 0xd746 no-refs, got bits={codeQ.bits} refs={codeQ.refs.size}")

        let rawBits : BitString :=
          natToBits schkBitsWord 16 ++
          natToBits schkRefsWord 16 ++
          natToBits schkBitRefsWord 16 ++
          natToBits schkBitsQWord 16 ++
          natToBits schkRefsQWord 16 ++
          natToBits schkBitRefsQWord 16 ++
          natToBits 0xa0 8
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-schkbits" r0 schkBitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-schkrefs" r1 schkRefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-schkbitrefs" r2 schkBitRefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-schkbitsq" r3 schkBitsQInstr 16
        let r5 ← expectDecodeStep "decode/raw-schkrefsq" r4 schkRefsQInstr 16
        let r6 ← expectDecodeStep "decode/raw-schkbitrefsq" r5 schkBitRefsQInstr 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback-vs-target-hit"
      run := do
        expectOkStack "dispatch/non-cell-op-falls-through"
          (runSchkRefsQDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-non-schkrefs-falls-through"
          (runSchkRefsQDispatchFallback schkBitsQInstr #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/target-hit-no-sentinel"
          (runSchkRefsQDispatchFallback schkRefsQInstr
            #[.slice oracleNoiseSlice, .slice oracleSliceRefs2, intV 2])
          #[.slice oracleNoiseSlice, intV (-1)]
        expectErr "dispatch/target-hit-error-no-sentinel"
          (runSchkRefsQDispatchFallback schkRefsQInstr #[.null, intV 0])
          .typeChk }
  ]
  oracle := #[
    mkSchkRefsQCase "ok/direct/refs0-need0"
      #[.slice oracleSliceRefs0, intV 0],
    mkSchkRefsQCase "ok/direct/refs1-need1"
      #[.slice oracleSliceRefs1, intV 1],
    mkSchkRefsQCase "ok/direct/refs3-need2"
      #[.slice oracleSliceRefs3, intV 2],
    mkSchkRefsQCase "ok/direct/refs4-need4"
      #[.slice oracleSliceRefs4, intV 4],
    mkSchkRefsQCase "ok/direct/refs3-need3"
      #[.slice oracleSliceRefs3, intV 3],

    mkSchkRefsQCase "fail/direct/refs0-need1"
      #[.slice oracleSliceRefs0, intV 1],
    mkSchkRefsQCase "fail/direct/refs1-need2"
      #[.slice oracleSliceRefs1, intV 2],
    mkSchkRefsQCase "fail/direct/refs4-need5"
      #[.slice oracleSliceRefs4, intV 5],
    mkSchkRefsQCase "fail/direct/refs4-need1023"
      #[.slice oracleSliceRefs4, intV 1023],
    mkSchkRefsQCase "fail/direct/refs3-need4"
      #[.slice oracleSliceRefs3, intV 4],

    mkSchkRefsQCase "underflow/empty" #[],
    mkSchkRefsQCase "underflow/one-item"
      #[.slice oracleSliceRefs1],
    mkSchkRefsQCase "type/refs-top-not-int"
      #[.slice oracleSliceRefs1, .null],
    mkSchkRefsQCase "range/refs-negative"
      #[.slice oracleSliceRefs1, intV (-1)],
    mkSchkRefsQCase "range/refs-gt1023"
      #[.slice oracleSliceRefs1, intV 1024],
    mkSchkRefsQCase "type/slice-not-slice"
      #[.null, intV 0],
    mkSchkRefsQCase "order/refs-range-before-slice-type"
      #[.null, intV 1024],
    mkSchkRefsQCase "order/refs-type-before-slice-type"
      #[.null, .null],
    mkSchkRefsQProgramCase "range/refs-nan-via-program" #[] schkProgramRefsNan,

    mkSchkRefsQCase "gas/exact-cost-succeeds"
      #[.slice oracleSliceRefs4, intV 0]
      #[.pushInt (.num schkRefsQSetGasExact), .tonEnvOp .setGasLimit, schkRefsQInstr],
    mkSchkRefsQCase "gas/exact-minus-one-out-of-gas"
      #[.slice oracleSliceRefs4, intV 0]
      #[.pushInt (.num schkRefsQSetGasExactMinusOne), .tonEnvOp .setGasLimit, schkRefsQInstr],

    mkSchkRefsQProgramCase "ok/program/srefs3-need1" #[]
      (mkSchkRefsQProgram 3 1),
    mkSchkRefsQProgramCase "fail/program/srefs3-need4" #[]
      (mkSchkRefsQProgram 3 4),
    mkSchkRefsQProgramCase "fail/program/srefs0-need1023" #[]
      (mkSchkRefsQProgram 0 1023)
  ]
  fuzz := #[
    { seed := 2026021046
      count := 320
      gen := genSchkRefsQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKREFSQ
