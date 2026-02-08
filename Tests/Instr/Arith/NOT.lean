import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.NOT

/-
NOT branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Not.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_not`, opcode registration in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/refint.cpp`
    (`operator~`)

Branch counts used for this suite:
- Lean: 5 branch points / 6 terminal outcomes
  (opcode dispatch; `VM.popInt` underflow/type/success; NaN-vs-num split;
   numeric `intToBitsTwos` success-vs-range error; non-quiet `pushIntQuiet`).
- C++: 4 branch points / 6 aligned terminal outcomes
  (registration binds NOT to `exec_not(..., quiet=false)`; `check_underflow(1)`;
   `pop_int` type check; `push_int_quiet` fit/NaN guard).

Key risk areas:
- Two's-complement boundary behavior at `minInt257` and `maxInt257`.
- Non-quiet NaN handling must throw `intOv` (NaN injected via `PUSHINT .nan`).
- Unary error ordering: underflow before type check; top-of-stack type check before below items.
- Exact gas boundary for `PUSHINT n; SETGASLIMIT; NOT`.
-/

private def notId : InstrId := { name := "NOT" }

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.not_])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := notId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runNotDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithNot .not_ stack

private def runNotDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithNot .add (VM.push (intV 777)) stack

private def notSetGasExact : Int :=
  computeExactGasBudget .not_

private def notSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne .not_

private def notBoundaryPool : Array Int :=
  #[
    minInt257,
    minInt257 + 1,
    minInt257 + 2,
    -(pow2 255),
    -1,
    0,
    1,
    (pow2 255) - 1,
    maxInt257 - 2,
    maxInt257 - 1,
    maxInt257
  ]

private def pickNotBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (notBoundaryPool.size - 1)
  (notBoundaryPool[idx]!, rng')

private def not257 (value : Int) : Int :=
  -value - 1

private def genNotFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  let (value, rng2) :=
    if shape = 0 then
      pickInt257Boundary rng1
    else if shape = 1 then
      pickSigned257ish rng1
    else if shape = 2 then
      let (pickMax, rng') := randBool rng1
      ((if pickMax then maxInt257 else minInt257), rng')
    else if shape = 3 then
      pickNotBoundary rng1
    else if shape = 4 then
      let (u, rng') := randNat rng1 0 20
      (Int.ofNat u - 10, rng')
    else if shape = 5 then
      let (base, rng') := pickSigned257ish rng1
      let adjusted :=
        if base = maxInt257 then maxInt257 - 1
        else if base = minInt257 then minInt257 + 1
        else base
      (adjusted, rng')
    else
      let (base, rng') := pickInt257Boundary rng1
      (not257 base, rng')
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV value], rng3)

def suite : InstrSuite where
  id := notId
  unit := #[
    { name := "unit/twos-complement-known-values"
      run := do
        let checks : Array Int :=
          #[
            minInt257,
            minInt257 + 1,
            minInt257 + 2,
            -(pow2 255),
            -7,
            -1,
            0,
            1,
            7,
            (pow2 255) - 1,
            maxInt257 - 1,
            maxInt257
          ]
        for value in checks do
          let expected := not257 value
          expectOkStack s!"not {value}" (runNotDirect #[intV value]) #[intV expected] }
    ,
    { name := "unit/error-order-underflow-type-and-top-selection"
      run := do
        expectErr "underflow/empty" (runNotDirect #[]) .stkUnd
        expectErr "type/top-null" (runNotDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runNotDirect #[.cell Cell.empty]) .typeChk
        expectErr "error-order/top-non-int-before-lower-int"
          (runNotDirect #[intV 9, .null]) .typeChk
        expectOkStack "error-order/top-int-lower-non-int-untouched"
          (runNotDirect #[.null, intV 9]) #[.null, intV (not257 9)] }
    ,
    { name := "unit/dispatch/non-not-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runNotDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive" #[intV 23],
    mkCase "ok/negative" #[intV (-23)],
    mkCase "ok/involution-double-not" #[intV 123456789] #[.not_, .not_],
    mkCase "boundary/min-int257" #[intV minInt257],
    mkCase "boundary/min-plus-one" #[intV (minInt257 + 1)],
    mkCase "boundary/max-int257" #[intV maxInt257],
    mkCase "boundary/max-minus-one" #[intV (maxInt257 - 1)],
    mkCase "pattern/high-bit-negative" #[intV (-(pow2 255))],
    mkCase "pattern/high-bit-minus-one" #[intV ((pow2 255) - 1)],
    mkCase "underflow/empty" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-lower-int" #[intV 9, .null],
    mkCase "error-order/top-int-lower-non-int-untouched" #[.null, intV 9],
    mkCase "nan/pushnan-intov" #[] #[.pushInt .nan, .not_],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num notSetGasExact), .tonEnvOp .setGasLimit, .not_],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num notSetGasExactMinusOne), .tonEnvOp .setGasLimit, .not_]
  ]
  fuzz := #[
    { seed := 2026020813
      count := 500
      gen := genNotFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.NOT
