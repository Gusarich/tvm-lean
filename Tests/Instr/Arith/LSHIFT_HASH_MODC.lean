import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.LSHIFT_HASH_MODC

/-
LSHIFT#MODC branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 2 1 false false (some z)` specialization)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeArithExtInstr`, `0xa9d8..0xa9da` with immediate `z` in `[1, 256]`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits`, hash decode family `0xa9d8..0xa9da`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, underflow/type behavior, non-quiet `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, `dump_shldivmod`, `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::mod_div_any`, ceil rounding)

Branch/terminal counts used for this suite (`d=2`, `roundMode=1`, `add=false`,
`quiet=false`, `zOpt=some`):
- Lean specialization: 7 branch sites / 9 terminal outcomes
  (dispatch/fallback; arity precheck; immediate-shift range gate; `y` pop type;
   `x` pop type; numeric-vs-invalid split; divisor-zero split; remainder push
   success-vs-`intOv`).
- C++ specialization: 6 branch sites / 9 aligned terminal outcomes
  (`check_underflow(2)`; const-shift validity; `pop_int` for divisor/numerator;
   division path and integer push fit-vs-overflow behavior).

Key risk areas covered:
- ceil-remainder sign behavior for mixed-sign and near-zero numerators;
- fixed immediate boundaries (`z = 1`, `z = 256`) plus decode correctness;
- explicit pop order (`y` first, then `x`) and below-stack preservation;
- underflow/type/error ordering, including malformed-immediate range-gate
  precedence in direct-handler tests;
- non-quiet NaN/invalid funnels (`divzero`, NaN operands, pre-op overflowed `PUSHINT`);
- exact gas cliff for `PUSHINT n; SETGASLIMIT; LSHIFT#MODC`.
-/

private def lshiftHashModcId : InstrId := { name := "LSHIFT#MODC" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkLshiftHashModcInstr (shift : Nat) : Instr :=
  .arithExt (.shlDivMod 2 1 false false (some shift))

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := lshiftHashModcId
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
  mkCase name stack #[mkLshiftHashModcInstr shift] gasLimits fuel

private def mkShiftInputCase
    (name : String)
    (shift : Nat)
    (vals : Array IntVal)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let instr := mkLshiftHashModcInstr shift
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix.push instr) gasLimits fuel

private def runLshiftHashModcDirect (shift : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt (mkLshiftHashModcInstr shift) stack

private def runLshiftHashModcDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5527)) stack

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

private def lshiftHashModcGasProbeInstr : Instr :=
  mkLshiftHashModcInstr 7

private def lshiftHashModcSetGasExact : Int :=
  computeExactGasBudget lshiftHashModcGasProbeInstr

private def lshiftHashModcSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne lshiftHashModcGasProbeInstr

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def shiftBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def ceilNumeratorPool : Array Int :=
  #[-9, -7, -5, -3, -1, 1, 3, 5, 7, 9]

private def smallDivisorPool : Array Int :=
  #[-7, -5, -3, -2, -1, 1, 2, 3, 5, 7]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickIntFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  pickNatFromPool shiftBoundaryPool rng

private def pickShiftInRange (rng : StdGen) : Nat × StdGen :=
  randNat rng 1 256

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pickNull, rng') := randBool rng
  ((if pickNull then .null else .cell Cell.empty), rng')

private def classifyLshiftHashModc (x y : Int) (shift : Nat) : String :=
  if y = 0 then
    "divzero"
  else
    let tmp : Int := x * intPow2 shift
    let (_, r) := divModRound tmp y 1
    if r = 0 then
      "ok/exact"
    else
      "ok/inexact"

private def mkFiniteFuzzCase (shape : Nat) (x y : Int) (shift : Nat) : OracleCase :=
  let kind := classifyLshiftHashModc x y shift
  mkShiftCase s!"/fuzz/shape-{shape}/{kind}" shift #[intV x, intV y]

private def genLshiftHashModcFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 22
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y0, r3) := pickInt257Boundary r2
      let y := if y0 = 0 then 1 else y0
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftInRange r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 2 then
      let (x, r2) := pickIntFromPool ceilNumeratorPool rng1
      let (y, r3) := pickIntFromPool smallDivisorPool r2
      let (shift, r4) := pickShiftBoundary r3
      (mkFiniteFuzzCase shape x y shift, r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftInRange r2
      (mkShiftCase s!"/fuzz/shape-{shape}/divzero" shift #[intV x, intV 0], r3)
    else if shape = 4 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/empty" shift #[], r2)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftCase s!"/fuzz/shape-{shape}/underflow/one-item" shift #[intV x], r3)
    else if shape = 6 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/underflow-before-type-single-non-int"
        shift #[.null], r2)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      let (yLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/y-top-non-int" shift #[intV x, yLike], r4)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      let (xLike, r4) := pickNonInt r3
      (mkShiftCase s!"/fuzz/shape-{shape}/type/x-second-non-int" shift #[xLike, intV y], r4)
    else if shape = 9 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/error-order/both-non-int-y-first"
        shift #[.null, .cell Cell.empty], r2)
    else if shape = 10 then
      let (x, r2) := pickIntFromPool ceilNumeratorPool rng1
      let (pickNull, r3) := randBool r2
      let below : Value := if pickNull then .null else .cell Cell.empty
      let (shift, r4) := randNat r3 1 4
      (mkShiftCase s!"/fuzz/shape-{shape}/pop-order/below-preserved"
        shift #[below, intV x, intV 3], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/y-via-program" shift #[.num x, .nan], r3)
    else if shape = 12 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftBoundary r2
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/x-via-program" shift #[.nan, .num y], r3)
    else if shape = 13 then
      let (shift, r2) := pickShiftBoundary rng1
      (mkShiftInputCase s!"/fuzz/shape-{shape}/nan/both-via-program" shift #[.nan, .nan], r2)
    else if shape = 14 then
      let (xo, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        shift #[.num xo, .num y], r4)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (yo, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftBoundary r3
      (mkShiftInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        shift #[.num x, .num yo], r4)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkFiniteFuzzCase shape x y 256, r3)
    else if shape = 17 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickIntFromPool smallDivisorPool r2
      (mkFiniteFuzzCase shape x y 1, r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      (mkShiftCase s!"/fuzz/shape-{shape}/divzero/shift256" 256 #[intV x, intV 0], r2)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      (mkFiniteFuzzCase shape x 1 1, r2)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      (mkFiniteFuzzCase shape x 2 1, r2)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      (mkFiniteFuzzCase shape x (-2) 1, r2)
    else
      let (pickMin, r2) := randBool rng1
      let x := if pickMin then minInt257 else maxInt257
      let (negDiv, r3) := randBool r2
      let y : Int := if negDiv then -7 else 7
      (mkFiniteFuzzCase shape x y 256, r3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := lshiftHashModcId
  unit := #[
    { name := "/unit/direct/ceil-remainder-sign-and-inexact-cases"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (7, 3, 1, -1),
            (-7, 3, 1, -2),
            (7, -3, 1, 2),
            (-7, -3, 1, 1),
            (1, 3, 1, -1),
            (-1, 3, 1, -2),
            (1, -3, 1, 2),
            (-1, -3, 1, 1),
            (5, 7, 2, -1),
            (-5, 7, 2, -6),
            (5, -7, 2, 6),
            (-5, -7, 2, 1),
            (6, 3, 1, 0),
            (0, 5, 256, 0)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"/unit/direct/x={x}/y={y}/z={shift}"
            (runLshiftHashModcDirect shift #[intV x, intV y]) #[intV expected] }
    ,
    { name := "/unit/direct/boundary-huge-quotient-and-pop-order"
      run := do
        let checks : Array (Int × Int × Nat × Int) :=
          #[
            (maxInt257, 1, 256, 0),
            (minInt257, 1, 256, 0),
            (maxInt257, 7, 256, -5),
            (maxInt257, -7, 256, 2),
            (minInt257, 7, 256, -4),
            (minInt257, -7, 256, 3),
            (minInt257 + 1, 7, 256, -2),
            (minInt257 + 1, -7, 256, 5)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let shift := c.2.2.1
          let expected := c.2.2.2
          expectOkStack s!"/unit/boundary/x={x}/y={y}/z={shift}"
            (runLshiftHashModcDirect shift #[intV x, intV y]) #[intV expected]
        expectOkStack "/unit/pop-order/below-null-preserved"
          (runLshiftHashModcDirect 1 #[.null, intV 7, intV 3]) #[.null, intV (-1)]
        expectOkStack "/unit/pop-order/below-cell-preserved"
          (runLshiftHashModcDirect 2 #[.cell Cell.empty, intV (-5), intV 7])
          #[.cell Cell.empty, intV (-6)] }
    ,
    { name := "/unit/error/divzero-underflow-type-and-pop-order"
      run := do
        expectErr "/unit/divzero/nonzero-over-zero"
          (runLshiftHashModcDirect 1 #[intV 5, intV 0]) .intOv
        expectErr "/unit/divzero/zero-over-zero"
          (runLshiftHashModcDirect 256 #[intV 0, intV 0]) .intOv
        expectErr "/unit/underflow/empty"
          (runLshiftHashModcDirect 1 #[]) .stkUnd
        expectErr "/unit/underflow/one-item"
          (runLshiftHashModcDirect 1 #[intV 1]) .stkUnd
        expectErr "/unit/error-order/underflow-before-type-single-non-int"
          (runLshiftHashModcDirect 1 #[.null]) .stkUnd
        expectErr "/unit/type/pop-y-first-null"
          (runLshiftHashModcDirect 1 #[intV 5, .null]) .typeChk
        expectErr "/unit/type/pop-y-first-cell"
          (runLshiftHashModcDirect 1 #[intV 5, .cell Cell.empty]) .typeChk
        expectErr "/unit/type/pop-x-second-null"
          (runLshiftHashModcDirect 1 #[.null, intV 5]) .typeChk
        expectErr "/unit/error-order/pop-y-before-x-when-both-non-int"
          (runLshiftHashModcDirect 1 #[.null, .cell Cell.empty]) .typeChk }
    ,
    { name := "/unit/error/immediate-range-gate-before-pop"
      run := do
        expectErr "/unit/range/shift0-before-y-pop"
          (runLshiftHashModcDirect 0 #[.null, .cell Cell.empty]) .typeChk
        expectErr "/unit/range/shift257-before-y-pop"
          (runLshiftHashModcDirect 257 #[.cell Cell.empty, .null]) .rangeChk
        expectErr "/unit/error-order/underflow-before-range-empty"
          (runLshiftHashModcDirect 0 #[]) .stkUnd
        expectErr "/unit/error-order/underflow-before-range-singleton"
          (runLshiftHashModcDirect 257 #[intV 7]) .stkUnd }
    ,
    { name := "/unit/opcode/decode-hash-sequence"
      run := do
        let instr1 := mkLshiftHashModcInstr 1
        let instr256 := mkLshiftHashModcInstr 256
        let program : Array Instr := #[instr1, instr256, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/lshift-hash-modc-z1" s0 instr1 24
        let s2 ← expectDecodeStep "/unit/decode/lshift-hash-modc-z256" s1 instr256 24
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-lshift-hash-modc-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runLshiftHashModcDispatchFallback #[]) #[intV 5527] }
  ]
  oracle := #[
    mkShiftInputCase "/ok/ceil/sign/pos-pos-shift1-inexact" 1 #[.num 7, .num 3],
    mkShiftInputCase "/ok/ceil/sign/neg-pos-shift1-inexact" 1 #[.num (-7), .num 3],
    mkShiftInputCase "/ok/ceil/sign/pos-neg-shift1-inexact" 1 #[.num 7, .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/neg-neg-shift1-inexact" 1 #[.num (-7), .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/near-zero-pos-divisor" 1 #[.num 1, .num 3],
    mkShiftInputCase "/ok/ceil/sign/near-zero-neg-divisor" 1 #[.num 1, .num (-3)],
    mkShiftInputCase "/ok/ceil/sign/near-zero-neg-numerator-pos-divisor" 1 #[.num (-1), .num 3],
    mkShiftInputCase "/ok/ceil/sign/near-zero-neg-numerator-neg-divisor" 1 #[.num (-1), .num (-3)],
    mkShiftInputCase "/ok/exact/divisible-shift1" 1 #[.num 6, .num 3],
    mkShiftInputCase "/ok/exact/divisible-neg-shift1" 1 #[.num (-6), .num 3],
    mkShiftInputCase "/ok/exact/zero-numerator-large-shift" 256 #[.num 0, .num 5],
    mkShiftInputCase "/ok/boundary/max-shift256-div1" 256 #[.num maxInt257, .num 1],
    mkShiftInputCase "/ok/boundary/min-shift256-div1" 256 #[.num minInt257, .num 1],
    mkShiftInputCase "/ok/boundary/max-shift256-div7" 256 #[.num maxInt257, .num 7],
    mkShiftInputCase "/ok/boundary/max-shift256-div-neg7" 256 #[.num maxInt257, .num (-7)],
    mkShiftInputCase "/ok/boundary/min-shift256-div7" 256 #[.num minInt257, .num 7],
    mkShiftInputCase "/ok/boundary/min-shift256-div-neg7" 256 #[.num minInt257, .num (-7)],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256-div7" 256 #[.num (minInt257 + 1), .num 7],
    mkShiftInputCase "/ok/boundary/min-plus-one-shift256-div-neg7" 256 #[.num (minInt257 + 1), .num (-7)],
    mkShiftCase "/ok/pop-order/below-null-preserved" 1 #[.null, intV 7, intV 3],
    mkShiftCase "/ok/pop-order/below-cell-preserved" 2 #[.cell Cell.empty, intV (-5), intV 7],
    mkShiftInputCase "/divzero/nonzero-over-zero" 1 #[.num 5, .num 0],
    mkShiftInputCase "/divzero/zero-over-zero-shift256" 256 #[.num 0, .num 0],
    mkShiftCase "/underflow/empty-stack" 1 #[],
    mkShiftCase "/underflow/one-item" 1 #[intV 1],
    mkShiftCase "/error-order/underflow-before-type-single-non-int" 1 #[.null],
    mkShiftCase "/type/pop-y-first-null" 1 #[intV 5, .null],
    mkShiftCase "/type/pop-y-first-cell" 1 #[intV 5, .cell Cell.empty],
    mkShiftCase "/type/pop-x-second-null" 1 #[.null, intV 5],
    mkShiftCase "/error-order/pop-y-before-x-when-both-non-int" 1 #[.null, .cell Cell.empty],
    mkShiftInputCase "/nan/y-via-program" 1 #[.num 7, .nan],
    mkShiftInputCase "/nan/x-via-program" 1 #[.nan, .num 3],
    mkShiftInputCase "/nan/both-via-program" 1 #[.nan, .nan],
    mkShiftInputCase "/error-order/pushint-overflow-x-before-op" 1 #[.num (maxInt257 + 1), .num 3],
    mkShiftInputCase "/error-order/pushint-overflow-y-before-op" 1 #[.num 7, .num (maxInt257 + 1)],
    mkShiftInputCase "/error-order/pushint-overflow-both-before-op"
      1 #[.num (maxInt257 + 1), .num (minInt257 - 1)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModcSetGasExact), .tonEnvOp .setGasLimit, lshiftHashModcGasProbeInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3]
      #[.pushInt (.num lshiftHashModcSetGasExactMinusOne), .tonEnvOp .setGasLimit, lshiftHashModcGasProbeInstr]
  ]
  fuzz := #[
    { seed := 2026020888
      count := 700
      gen := genLshiftHashModcFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_MODC
