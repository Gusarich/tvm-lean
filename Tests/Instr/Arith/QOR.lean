import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QOR

/-
QOR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`execInstrArithContExt`, `.qor`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_or`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 8 branch points / 9 terminal outcomes
  (instruction/opcode dispatch gates; explicit underflow guard; two pop/type checks;
   NaN-left/NaN-right/finite split; two signed-257 conversion checks).
- C++: 6 branch points / 7 aligned terminal outcomes
  (opcode dispatch to `exec_or(..., quiet=true)`; underflow guard; two `pop_int` type checks;
   modern NaN guard; quiet push path).

Key risk areas:
- underflow must be checked before any pop/type work (`check_underflow(2)` ordering);
- pop order remains `y` then `x` for type-check precedence;
- quiet NaN propagation must succeed (no `intOv`);
- two's-complement OR behavior around `±2^255` and full 257-bit boundaries;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QOR` (exact vs exact-minus-one).
-/

private def qorId : InstrId := { name := "QOR" }

private def qorInstr : Instr := .contExt .qor

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qorInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qorId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, programPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name (below ++ stackOrEmpty) (programPrefix ++ #[qorInstr])

private def runQorDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qorInstr stack

private def runQorDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 31337)) stack

private def qorSetGasExact : Int :=
  computeExactGasBudget qorInstr

private def qorSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qorInstr

private def genQorFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, r3) := pickInt257Boundary rng2
    let (y, r4) := pickInt257Boundary r3
    (mkInputCase s!"fuzz/ok/boundary-boundary-{tag}" (.num x) (.num y), r4)
  else if shape = 1 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickSigned257ish r3
    (mkInputCase s!"fuzz/ok/signed-signed-{tag}" (.num x) (.num y), r4)
  else if shape = 2 then
    let (x, r3) := pickInt257Boundary rng2
    let (y, r4) := pickSigned257ish r3
    (mkInputCase s!"fuzz/ok/boundary-signed-{tag}" (.num x) (.num y), r4)
  else if shape = 3 then
    let (x, r3) := pickSigned257ish rng2
    let (y, r4) := pickInt257Boundary r3
    (mkInputCase s!"fuzz/ok/signed-boundary-{tag}" (.num x) (.num y), r4)
  else if shape = 4 then
    let (y, r3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/zero-left-{tag}" (.num 0) (.num y), r3)
  else if shape = 5 then
    let (x, r3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/zero-right-{tag}" (.num x) (.num 0), r3)
  else if shape = 6 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else if shape = 7 then
    (mkCase s!"fuzz/error-order/one-arg-non-int-underflow-{tag}" #[.null], rng2)
  else if shape = 8 then
    let (x, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/type/pop-y-first-{tag}" #[intV x, .null], r3)
  else if shape = 9 then
    let (y, r3) := pickSigned257ish rng2
    (mkCase s!"fuzz/type/pop-x-second-{tag}" #[.null, intV y], r3)
  else if shape = 10 then
    (mkCase s!"fuzz/error-order/both-non-int-{tag}" #[.cell Cell.empty, .null], rng2)
  else
    let (x, r3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/nan/pushnan-y-{tag}" (.num x) .nan, r3)

def suite : InstrSuite where
  id := qorId
  unit := #[
    { name := "unit/ok/twos-complement-patterns"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (0, 137, 137),
            (137, 0, 137),
            (-1, 0, -1),
            (-1, 137, -1),
            (-8, 3, -5),
            (-8, 7, -1),
            (-16, 7, -9),
            (minInt257, 0, minInt257),
            (maxInt257, 0, maxInt257),
            (maxInt257, minInt257, -1),
            (minInt257, 1, minInt257 + 1),
            (-(pow2 255), (pow2 255) - 1, -1),
            (-(pow2 200), pow2 13, (-(pow2 200)) + (pow2 13))
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x}|{y}" (runQorDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/error-order/underflow-before-type-and-pop-order"
      run := do
        expectErr "underflow/empty" (runQorDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQorDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQorDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first" (runQorDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second" (runQorDirect #[.null, intV 1]) .typeChk
        expectErr "type/both-non-int-y-first" (runQorDirect #[.cell Cell.empty, .null]) .typeChk
        expectOkStack "error-order/top-two-only-lower-preserved"
          (runQorDirect #[.null, intV (-8), intV 7]) #[.null, intV (-1)] }
    ,
    { name := "unit/nan-and-range/quiet-nan-and-conversion-rangechk"
      run := do
        expectOkStack "nan/x" (runQorDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y" (runQorDirect #[intV 1, .int .nan]) #[.int .nan]
        expectErr "range/x-out-of-range-positive" (runQorDirect #[intV (pow2 256), intV 0]) .rangeChk
        expectErr "range/y-out-of-range-negative"
          (runQorDirect #[intV 0, intV (-(pow2 256) - 1)]) .rangeChk }
    ,
    { name := "unit/dispatch/non-qor-falls-through"
      run := do
        expectOkStack "fallback/non-contExt" (runQorDispatchFallback .add #[]) #[intV 31337]
        expectOkStack "fallback/other-contExt" (runQorDispatchFallback (.contExt .condSel) #[]) #[intV 31337] }
  ]
  oracle := #[
    mkInputCase "ok/zero-zero" (.num 0) (.num 0),
    mkInputCase "ok/zero-left" (.num 0) (.num 137),
    mkInputCase "ok/zero-right" (.num 137) (.num 0),
    mkInputCase "ok/sign/pos-pos" (.num 17) (.num 25),
    mkInputCase "ok/sign/pos-neg" (.num 17) (.num (-5)),
    mkInputCase "ok/sign/neg-pos" (.num (-17)) (.num 5),
    mkInputCase "ok/sign/neg-neg" (.num (-17)) (.num (-5)),
    mkInputCase "ok/bitpattern/neg8-or-3" (.num (-8)) (.num 3),
    mkInputCase "ok/bitpattern/neg8-or-7" (.num (-8)) (.num 7),
    mkInputCase "ok/boundary/min-or-zero" (.num minInt257) (.num 0),
    mkInputCase "ok/boundary/max-or-zero" (.num maxInt257) (.num 0),
    mkInputCase "ok/boundary/max-or-min-all-ones" (.num maxInt257) (.num minInt257),
    mkInputCase "ok/boundary/min-or-one" (.num minInt257) (.num 1),
    mkInputCase "ok/boundary/neg2pow255-or-mask" (.num (-(pow2 255))) (.num ((pow2 255) - 1)),
    mkInputCase "ok/minus-one-or-random" (.num (-1)) (.num 424242),
    mkInputCase "error-order/top-two-only-lower-preserved" (.num (-8)) (.num 7) #[.null],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg-int" #[intV 1],
    mkCase "error-order/one-arg-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkInputCase "nan/pushnan-y" (.num 7) .nan,
    mkInputCase "nan/pushnan-x" .nan (.num 7),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qorSetGasExact), .tonEnvOp .setGasLimit, qorInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qorSetGasExactMinusOne), .tonEnvOp .setGasLimit, qorInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 500
      gen := genQorFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QOR
