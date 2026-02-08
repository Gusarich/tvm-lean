import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.BITSIZE

/-
BITSIZE branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Bitsize.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_bitsize`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`Stack::pop_int`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::bit_size_any`, signed-bit-width computation)

Branch map used for this suite:
- Lean: 5 branch points / 8 terminal outcomes
  (opcode dispatch; unary pop underflow/type/success; NaN-vs-num split;
   signed width split on `n = 0`, `n > 0`, `n < 0`; stack push success).
- C++: 5 branch points / 8 aligned terminal outcomes for BITSIZE
  (underflow guard; `pop_int` type check; `bit_size(true)` finite-vs-sentinel;
   non-quiet sentinel throw path; finite width push path).

Key risk areas:
- NaN handling divergence risk: non-quiet BITSIZE must throw `rangeChk` (not `intOv`).
- Signed-width boundary off-by-one around `-1/0/1`, `±2^255`, and `[-2^256, 2^256-1]`.
- Unary pop/error ordering: empty stack underflow vs top non-int type check.
- Top-only pop behavior: lower stack entries must remain untouched on success/error.
- Exact gas threshold via `PUSHINT n; SETGASLIMIT; BITSIZE`.
-/

private def bitsizeId : InstrId := { name := "BITSIZE" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.bitsize])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bitsizeId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBitsizeDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithBitsize .bitsize stack

private def runBitsizeDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithBitsize .add (VM.push (intV 777)) stack

private def bitsizeSetGasExact : Int :=
  computeExactGasBudget .bitsize

private def bitsizeSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .bitsize

private def bitsizeBoundaryPool : Array Int :=
  #[
    0, 1, -1, 2, -2, 3, -3,
    (pow2 255) - 1, -(pow2 255), pow2 255, -(pow2 255) - 1,
    maxInt257, maxInt257 - 1, minInt257, minInt257 + 1
  ]

private def pickBitsizeBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsizeBoundaryPool.size - 1)
  (bitsizeBoundaryPool[idx]!, rng')

private def genBitsizeFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickBitsizeBoundary rng2
    (mkCase s!"fuzz/ok/boundary-{tag}" #[intV x], rng3)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/ok/random-{tag}" #[intV x], rng3)
  else if shape = 2 then
    let (k, rng3) := randNat rng2 0 255
    let (variant, rng4) := randNat rng3 0 3
    let p := pow2 k
    let x : Int :=
      if variant = 0 then
        p - 1
      else if variant = 1 then
        p
      else if variant = 2 then
        -p
      else
        -p - 1
    (mkCase s!"fuzz/ok/pow2-edge-{tag}" #[intV x], rng4)
  else if shape = 3 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/error-order/top-int-lower-non-int-{tag}" #[.null, intV x], rng3)
  else if shape = 4 then
    let (v, rng3) := randNat rng2 0 1
    let top : Value := if v = 0 then .null else .cell Cell.empty
    let (x, rng4) := pickSigned257ish rng3
    (mkCase s!"fuzz/type/top-non-int-{tag}" #[intV x, top], rng4)
  else if shape = 5 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else
    let (v, rng3) := randNat rng2 0 1
    let top : Value := if v = 0 then .null else .cell Cell.empty
    (mkCase s!"fuzz/type/single-non-int-{tag}" #[top], rng3)

def suite : InstrSuite where
  id := bitsizeId
  unit := #[
    { name := "unit/known-signed-widths-and-boundaries"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 0),
            (1, 2),
            (-1, 1),
            (2, 3),
            (-2, 2),
            (7, 4),
            (-7, 4),
            ((pow2 255) - 1, 256),
            (-(pow2 255), 256),
            (pow2 255, 257),
            (-(pow2 255) - 1, 257),
            (maxInt257, 257),
            (minInt257, 257)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"bitsize {x}" (runBitsizeDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/nan-non-quiet-rangechk-regression"
      run := do
        expectErr "nan" (runBitsizeDirect #[.int .nan]) .rangeChk }
    ,
    { name := "unit/underflow-type-and-pop-ordering"
      run := do
        expectErr "empty-underflow" (runBitsizeDirect #[]) .stkUnd
        expectErr "top-null-typechk" (runBitsizeDirect #[.null]) .typeChk
        expectErr "top-cell-typechk" (runBitsizeDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runBitsizeDirect #[intV 9, .null]) .typeChk
        expectOkStack "top-int-lower-non-int-untouched"
          (runBitsizeDirect #[.null, intV (-7)])
          #[.null, intV 4] }
    ,
    { name := "unit/dispatch/non-bitsize-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runBitsizeDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive-small" #[intV 7],
    mkCase "ok/negative-small" #[intV (-7)],
    mkCase "ok/positive-power-minus-one" #[intV ((pow2 255) - 1)],
    mkCase "ok/negative-power" #[intV (-(pow2 255))],
    mkCase "boundary/max-int257" #[intV maxInt257],
    mkCase "boundary/min-int257" #[intV minInt257],
    mkCase "boundary/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "overflow/pushint-out-of-range-before-bitsize" #[]
      #[.pushInt (.num (pow2 256)), .bitsize],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-below-int" #[intV 9, .null],
    mkCase "error-order/top-int-lower-non-int-untouched" #[.null, intV (-7)],
    mkCase "range/nan-via-program-regression" #[] #[.pushInt .nan, .bitsize],
    mkCase "gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num bitsizeSetGasExact), .tonEnvOp .setGasLimit, .bitsize],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num bitsizeSetGasExactMinusOne), .tonEnvOp .setGasLimit, .bitsize]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 600
      gen := genBitsizeFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.BITSIZE
