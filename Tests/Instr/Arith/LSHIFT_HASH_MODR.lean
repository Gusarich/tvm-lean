import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_MODR

/-
LSHIFT#MODR branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 0 false false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, hash-immediate `0xa9d8..0xa9da` with `z ∈ [1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash decode family `0xa9d8..0xa9da`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior and pop ordering)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, nearest rounding)

Branch/terminal counts used for this suite (`d=2`, `roundMode=0`, `add=false`,
`quiet=false`, `zOpt=some`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; arity precheck; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-invalid split; divisor-zero split and non-quiet
   NaN funnel to `intOv`).
- C++ specialization: 6 branch sites / 9 aligned terminal outcomes
  (`check_underflow(2)`; const-shift validity; divisor/numerator `pop_int`;
   divisor-zero path; nearest remainder computation; non-quiet push behavior).

Key risk areas covered:
- nearest-rounding remainder behavior, including half ties and sign-mixed inputs;
- fixed-immediate boundaries (`z = 1`, `z = 256`) plus decode correctness;
- explicit pop order (`y` first, then `x`) and below-stack preservation;
- underflow/type/range ordering, including malformed-immediate precedence tests;
- non-quiet NaN/out-of-range funnels injected via `PUSHINT` prelude only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#MODR`.
-/

private def lshiftHashModrId : InstrId := { name := "LSHIFT#MODR" }

private def mkLshiftHashModrInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 2 0 false false (some shift))

private def lshiftHashModrInstrDefault : Instr :=
  mkLshiftHashModrInstr 1

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[lshiftHashModrInstrDefault])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := lshiftHashModrId
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
  mkCase name stack #[mkLshiftHashModrInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashModrInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashModrDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashModrInstr shift) stack

private def runLshiftHashModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5519)) stack

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

private def lshiftHashModrGasProbeInstr : Instr :=
  lshiftHashModrInstrDefault

private def lshiftHashModrSetGasExact : Int :=
  computeExactGasBudget lshiftHashModrGasProbeInstr

private def lshiftHashModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashModrGasProbeInstr

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

private def classifyLshiftHashModr (x y : Int) (shift : Nat) : String :=
  let tmp : Int := x * pow2 shift
  if y = 0 then
    "intov-divzero"
  else
    let (_, r) := divModRound tmp y 0
    if !intFitsSigned257 r then
      "intov-overflow"
    else if r = 0 then
      "ok-exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "ok-tie"
    else
      "ok-inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashModr x y shift
  mkShiftInputCase s!"/fuzz/shape-{shape}/{kind}" shift #[.num x, .num y]

private def genLshiftHashModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-divzero"
        shift #[.num x, .num 0], r3)
    else if shape = 3 then
      let (x, r2) := pickIntFromPool tieNumeratorPool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-tie-pos-den"
        1 #[.num x, .num 4], r2)
    else if shape = 4 then
      let (x, r2) := pickIntFromPool tieNumeratorPool rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-tie-neg-den"
        1 #[.num x, .num (-4)], r2)
    else if shape = 5 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow-empty" shift #[], r2)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow-one-item" shift #[intV x], r3)
    else if shape = 7 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      let (yLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type-y-top-non-int" shift #[intV x, yLike], r4)
    else if shape = 9 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftInRange r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type-x-second-non-int" shift #[xLike, intV y], r4)
    else if shape = 10 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-both-non-int-y-first"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 11 then
      let (shift, r2) := randNat rng1 1 4
      let (x, r3) := pickIntFromPool tieNumeratorPool r2
      let (pickNull, r4) := randBool r3
      let below : Value := if pickNull then .null else .cell Cell.empty
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order-below-preserved"
        shift #[below, intV x, intV 3], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-y-via-program"
        shift #[.num x, .nan], r3)
    else if shape = 13 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-x-via-program"
        shift #[.nan, .num y], r3)
    else if shape = 14 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-nan-both-via-program"
        shift #[.nan, .nan], r2)
    else if shape = 15 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-x-before-op"
        shift #[.num xo, .num y], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order-pushint-overflow-y-before-op"
        shift #[.num x, .num yo], r4)
    else if shape = 17 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-boundary-shift256"
        256 #[.num 1, .num 2], rng1)
    else if shape = 18 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-boundary-shift1-neg-den"
        1 #[.num 7, .num (-3)], rng1)
    else if shape = 19 then
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-exact-max-div2-shift1"
        1 #[.num maxInt257, .num 2], rng1)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/intov-divzero-shift256"
        256 #[.num x, .num 0], r2)
    else if shape = 21 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order-underflow-before-type-single-non-int-fixed"
        shift #[.cell Cell.empty], r2)
    else
      (mkShiftInputCase s!"/fuzz/shape-{shape}/ok-boundary-shift256-neg"
        256 #[.num (-1), .num 2], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashModrId
  unit := #[
    { name := "/unit/direct/nearest-rounding-sign-and-ties"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, -1),
            (-7, 3, 1, 1),
            (7, -3, 1, -1),
            (-7, -3, 1, 1),
            (5, 4, 1, -2),
            (-5, 4, 1, -2),
            (5, -4, 1, 2),
            (-5, -4, 1, 2),
            (1, 4, 1, -2),
            (-1, 4, 1, -2),
            (1, -4, 1, 2),
            (-1, -4, 1, 2),
            (21, 3, 1, 0),
            (-21, 3, 1, 0),
            (42, 7, 3, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, r) =>
              expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
                (runLshiftHashModrDirect shift #[intV x, intV y]) #[intV r] }
    ,
    { name := "/unit/direct/boundary-success-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 2, 1, 0),
            (minInt257, 2, 1, 0),
            (minInt257 + 1, -2, 1, 0),
            (1, 2, 256, 0),
            (-1, 2, 256, 0),
            (0, 5, 256, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, r) =>
              expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
                (runLshiftHashModrDirect shift #[intV x, intV y]) #[intV r]
        expectOkStack "/unit/pop-order/below-null"
          (runLshiftHashModrDirect 1 #[.null, intV 7, intV 3]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell"
          (runLshiftHashModrDirect 2 #[.cell Cell.empty, intV (-7), intV 3])
          #[.cell Cell.empty, intV (-1)] }
    ,
    { name := "/unit/error/divzero-underflow-type-and-order"
      run := do
        expectErr "/unit/intov/divzero/nonzero-over-zero"
          (runLshiftHashModrDirect 1 #[intV 5, intV 0]) .intOv
        expectErr "/unit/underflow/empty"
          (runLshiftHashModrDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-item"
          (runLshiftHashModrDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runLshiftHashModrDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/y-top-non-int"
          (runLshiftHashModrDirect 1 #[intV 7, .null]) .typeChk
        expectErr "/unit/type/x-second-non-int"
          (runLshiftHashModrDirect 1 #[.null, intV 7]) .typeChk
        expectErr "/unit/error-order/both-non-int-y-first"
          (runLshiftHashModrDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-before-pop"
      run := do
        expectErr "/unit/range/shift0-before-y-pop"
          (runLshiftHashModrDirect 0 #[.null, .cell Cell.empty]) .rangeChk
        expectErr "/unit/range/shift257-before-y-pop"
          (runLshiftHashModrDirect 257 #[.cell Cell.empty, .null]) .rangeChk
        expectErr "/unit/error-order/underflow-before-range-invalid-immediate"
          (runLshiftHashModrDirect 0 #[]) .stkUnd }
    ,
    { name := "/unit/opcode/decode-hash-sequence"
      run := do
        let instr1 := mkLshiftHashModrInstr 1
        let instr256 := mkLshiftHashModrInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"/unit/opcode/assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-modr-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-modr-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-modr-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashModrDispatchFallback #[]) #[intV 5519] }
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
    mkShiftInputCase "/intov/divzero/nonzero-over-zero" 1 #[.num 5, .num 0],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/y-top-non-int" 1 #[intV 7, .null],
    mkShiftCase "/type/x-second-non-int" 1 #[.null, intV 3],
    mkShiftCase "/error-order/both-non-int-y-first" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/intov/nan-y-via-program" 1 #[.num 7, .nan],
    mkShiftInputCase "/intov/nan-x-via-program" 1 #[.nan, .num 3],
    mkShiftInputCase "/intov/nan-both-via-program" 1 #[.nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op"
      1 #[.num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op"
      1 #[.num 7, .num (maxInt257 + 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModrSetGasExact), .tonEnvOp .setGasLimit, lshiftHashModrGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashModrGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020871
      count := 700
      gen := genLshiftHashModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_MODR
