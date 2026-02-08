import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_DIVR

/-
LSHIFT#DIVR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 1 0 false false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, `0xa9d4..0xa9d6` with immediate `z` in `[1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash decode family `0xa9d4..0xa9d6`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest rounding)

Branch/terminal counts used for this suite (`d=1`, `roundMode=0`, `add=false`,
`quiet=false`, `zOpt=some`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; arity precheck; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-invalid split; divisor-zero split; quotient push
   success-vs-`intOv`).
- C++ specialization: 6 branch sites / 9 aligned terminal outcomes
  (`check_underflow(2)`; const-shift validity; `pop_int` for divisor/numerator;
   division path and integer push fit-vs-overflow behavior).

Key risk areas covered:
- nearest rounding ties for `(x << z) / y` with sign-mixed operands;
- fixed immediate boundaries (`z = 1`, `z = 256`) plus decode correctness;
- explicit pop order (`y` first, then `x`) and below-stack preservation;
- underflow/type/error ordering, including malformed-immediate range gate
  precedence in direct handler tests;
- non-quiet NaN/invalid funnels (`divzero`, NaN operands, overflowed quotient);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#DIVR`.
-/

private def lshiftHashDivrId : InstrId := { name := "LSHIFT#DIVR" }

private def mkLshiftHashDivrInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 1 0 false false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftHashDivrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkShiftCase
    (name : String)
    (shift : Nat)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkLshiftHashDivrInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashDivrInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashDivrDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashDivrInstr shift) stack

private def runLshiftHashDivrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5507)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def lshiftHashDivrGasProbeInstr : Instr :=
  mkLshiftHashDivrInstr 7

private def lshiftHashDivrSetGasExact : Int :=
  computeExactGasBudget lshiftHashDivrGasProbeInstr

private def lshiftHashDivrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashDivrGasProbeInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def tieNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def genLshiftHashDivrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 21
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary" shift #[.num x, .num y], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/random" shift #[.num x, .num y], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/divzero" shift #[.num x, .num 0], r3)
    else if shape = 3 then
      let (x, r2) := pickIntFromPool tieNumeratorPool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/round/tie-pos-den" 1 #[.num x, .num 4], r2)
    else if shape = 4 then
      let (x, r2) := pickIntFromPool tieNumeratorPool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/round/tie-neg-den" 1 #[.num x, .num (-4)], r2)
    else if shape = 5 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/overflow/max-shift1-div1"
        1 #[.num maxInt257, .num 1], rng1)
    else if shape = 6 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/overflow/min-shift1-div1"
        1 #[.num minInt257, .num 1], rng1)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" shift #[intV x], r3)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/y-top-non-int" shift #[intV x, yLike], r4)
    else if shape = 11 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-second-non-int" shift #[xLike, intV y], r4)
    else if shape = 12 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/both-non-int-y-first"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 13 then
      let (shift, r2) := randNat rng1 1 4
      let (x, r3) := pickIntFromPool tieNumeratorPool r2
      let (pickNull, r4) := randBool r3
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV 3], r4)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/y-via-program" shift #[.num x, .nan], r3)
    else if shape = 15 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program" shift #[.nan, .num y], r3)
    else if shape = 16 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/both-via-program" shift #[.nan, .nan], r2)
    else if shape = 17 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xo, .num y], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num yo], r4)
    else if shape = 19 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary/shift256"
        256 #[.num 1, .num 2], rng1)
    else if shape = 20 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok/boundary/shift1-neg-den"
        1 #[.num 7, .num (-3)], rng1)
    else
      (mkShiftInputCase s!"/fuzz/shape-{shape}/divzero/shift256"
        256 #[.num 5, .num 0], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashDivrId
  unit := #[
    { name := "/unit/direct/nearest-rounding-sign-and-ties"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, 5),
            (-7, 3, 1, -5),
            (7, -3, 1, -5),
            (-7, -3, 1, 5),
            (5, 4, 1, 3),
            (-5, 4, 1, -2),
            (5, -4, 1, -2),
            (-5, -4, 1, 3),
            (1, 4, 1, 1),
            (-1, 4, 1, 0),
            (1, -4, 1, 0),
            (-1, -4, 1, 1),
            (21, 3, 1, 14),
            (-21, 3, 1, -14)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"x={x}/y={y}/z={shift}"
            (runLshiftHashDivrDirect shift #[intV x, intV y]) #[intV q] }
    ,
    { name := "/unit/direct/boundary-success-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 2, 1, maxInt257),
            (minInt257, 2, 1, minInt257),
            (minInt257 + 1, -2, 1, maxInt257),
            (1, 2, 256, pow2 255),
            (-1, 2, 256, -(pow2 255)),
            (0, 5, 256, 0),
            (42, 7, 3, 48)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let q := c.2.2.2
          expectOkStack s!"boundary/x={x}/y={y}/z={shift}"
            (runLshiftHashDivrDirect shift #[intV x, intV y]) #[intV q]
        expectOkStack "pop-order/below-null"
          (runLshiftHashDivrDirect 1 #[.null, intV 7, intV 3]) #[.null, intV 5]
        expectOkStack "pop-order/below-cell"
          (runLshiftHashDivrDirect 2 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-9)] }
    ,
    { name := "/unit/error/divzero-overflow-underflow-type-and-order"
      run := do
        expectErr "divzero/nonzero-over-zero"
          (runLshiftHashDivrDirect 1 #[intV 5, intV 0]) .intOv
        expectErr "overflow/max-shift1-div1"
          (runLshiftHashDivrDirect 1 #[intV maxInt257, intV 1]) .intOv
        expectErr "overflow/min-shift1-div1"
          (runLshiftHashDivrDirect 1 #[intV minInt257, intV 1]) .intOv
        expectErr "underflow/empty"
          (runLshiftHashDivrDirect 1 #[]) .stkUnd
        expectErr "underflow/one-item"
          (runLshiftHashDivrDirect 1 #[intV 1]) .stkUnd
        expectErr "error-order/underflow-before-type-single-non-int"
          (runLshiftHashDivrDirect 1 #[.null]) .stkUnd
        expectErr "type/y-top-non-int"
          (runLshiftHashDivrDirect 1 #[intV 7, .null]) .typeChk
        expectErr "type/x-second-non-int"
          (runLshiftHashDivrDirect 1 #[.null, intV 7]) .typeChk
        expectErr "error-order/both-non-int-y-first"
          (runLshiftHashDivrDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-before-pop"
      run := do
        expectErr "range/shift0-before-y-pop"
          (runLshiftHashDivrDirect 0 #[.null, .cell Cell.empty]) .rangeChk
        expectErr "range/shift257-before-y-pop"
          (runLshiftHashDivrDirect 257 #[.cell Cell.empty, .null]) .rangeChk
        expectErr "underflow/shift0-empty-before-range-gate"
          (runLshiftHashDivrDirect 0 #[]) .stkUnd }
    ,
    { name := "/unit/opcode/decode-hash-sequence"
      run := do
        let instr1 := mkLshiftHashDivrInstr 1
        let instr256 := mkLshiftHashDivrInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/lshift-hash-divr-z1" s0 instr1 24
        let s2 ← expectDecodeStep "decode/lshift-hash-divr-z256" s1 instr256 24
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-divr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLshiftHashDivrDispatchFallback #[]) #[intV 5507] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/round/pos-pos-inexact" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/round/neg-pos-inexact" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/round/pos-neg-inexact" 1 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/round/neg-neg-inexact" 1 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/tie/pos-pos-half" 1 #[.num 5, .num 4],
    mkShiftInputCase "/ok/tie/neg-pos-half" 1 #[.num (-5), .num 4],
    mkShiftInputCase "/ok/tie/pos-neg-half" 1 #[.num 5, .num (-4)],
    mkShiftInputCase "/ok/tie/neg-neg-half" 1 #[.num (-5), .num (-4)],
    mkShiftInputCase "/ok/tie/neg-pos-near-zero" 1 #[.num (-1), .num 4],
    mkShiftInputCase "/ok/tie/pos-neg-near-zero" 1 #[.num 1, .num (-4)],
    mkShiftInputCase "/ok/tie/neg-neg-near-zero" 1 #[.num (-1), .num (-4)],
    mkShiftInputCase "/ok/exact/shift1-pos-pos" 1 #[.num 21, .num 3],
    mkShiftInputCase "/ok/exact/shift1-neg-pos" 1 #[.num (-21), .num 3],
    mkShiftInputCase "/ok/exact/shift3-pos-pos" 3 #[.num 42, .num 7],
    mkShiftInputCase "/ok/exact/shift3-neg-pos" 3 #[.num (-42), .num 7],
    mkShiftInputCase "/ok/exact/zero-numerator-shift256" 256 #[.num 0, .num 5],
    mkShiftInputCase "/ok/boundary/max-div2-shift1" 1 #[.num maxInt257, .num 2],
    mkShiftInputCase "/ok/boundary/min-div2-shift1" 1 #[.num minInt257, .num 2],
    mkShiftInputCase "/ok/boundary/min-plus-one-div-neg2-shift1"
      1 #[.num (minInt257 + 1), .num (-2)],
    mkShiftInputCase "/ok/boundary/one-div2-shift256" 256 #[.num 1, .num 2],
    mkShiftInputCase "/ok/boundary/neg-one-div2-shift256" 256 #[.num (-1), .num 2],
    mkShiftCase "/ok/pop-order/below-preserved-null" 1 #[.null, intV 7, intV 3],
    mkShiftCase "/ok/pop-order/below-preserved-cell" 2 #[.cell Cell.empty, intV (-7), intV 3],
    mkShiftInputCase "/divzero/nonzero-over-zero" 1 #[.num 5, .num 0],
    mkShiftInputCase "/overflow/max-shift1-div1" 1 #[.num maxInt257, .num 1],
    mkShiftInputCase "/overflow/min-shift1-div1" 1 #[.num minInt257, .num 1],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/y-top-non-int" 1 #[intV 7, .null],
    mkShiftCase "/type/x-second-non-int" 1 #[.null, intV 3],
    mkShiftCase "/error-order/both-non-int-y-first" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/nan/y-via-program" 1 #[.num 7, .nan],
    mkShiftInputCase "/nan/x-via-program" 1 #[.nan, .num 3],
    mkShiftInputCase "/nan/both-via-program" 1 #[.nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 #[.num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 #[.num 7, .num (maxInt257 + 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivrSetGasExact), .tonEnvOp .setGasLimit, lshiftHashDivrGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashDivrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashDivrGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020847
      count := 700
      gen := genLshiftHashDivrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIVR
