import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QXOR

/-
QXOR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.contExt .qxor`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`checkUnderflow`, `popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_xor`, `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 8 branch points / 10 terminal outcomes
  (outer dispatch; `.qxor` dispatch; explicit `checkUnderflow 2`; two `popInt` checks;
   NaN-left/NaN-right/finite split; two `intToBitsTwos` conversions).
- C++: 5 branch points / 8 aligned terminal outcomes
  (`QXOR` opcode registration to `exec_xor(..., quiet=true)`; `check_underflow(2)`;
   two `pop_int` checks; `push_int_quiet` quiet push behavior).

Key risk areas:
- underflow-vs-type ordering for depth=1 stacks (`check_underflow(2)` must run first);
- operand pop order (`y` first, then `x`) determining type-check attribution;
- quiet NaN propagation (`QXOR` must push NaN, not throw `intOv`);
- two's-complement behavior at `minInt257`/`maxInt257` boundaries;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QXOR`.
-/

private def qxorId : InstrId := { name := "QXOR" }

private def qxorInstr : Instr := .contExt .qxor

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qxorInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qxorId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x y : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x, y]
  mkCase name (below ++ stackOrEmpty) (progPrefix.push qxorInstr)

private def runQXorDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qxorInstr stack

private def runQXorDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 31337)) stack

private def qxorSetGasExact : Int :=
  computeExactGasBudget qxorInstr

private def qxorSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qxorInstr

private def qxorOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQXorOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qxorOutOfRangePool.size - 1)
  (qxorOutOfRangePool[idx]!, rng')

private def pickQXorNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQXorFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickInt257Boundary rng2
    let (y, rng4) := pickInt257Boundary rng3
    (mkInputCase s!"fuzz/ok/boundary-{tag}" (.num x) (.num y), rng4)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    let (y, rng4) := pickSigned257ish rng3
    (mkInputCase s!"fuzz/ok/random-{tag}" (.num x) (.num y), rng4)
  else if shape = 2 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/zero-identity-{tag}" (.num x) (.num 0), rng3)
  else if shape = 3 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/negone-identity-{tag}" (.num x) (.num (-1)), rng3)
  else if shape = 4 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/self-cancel-{tag}" (.num x) (.num x), rng3)
  else if shape = 5 then
    let (x, rng3) := pickInt257Boundary rng2
    (mkInputCase s!"fuzz/ok/high-bit-{tag}" (.num x) (.num (pow2 255)), rng3)
  else if shape = 6 then
    let (y, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/nan/x-{tag}" .nan (.num y), rng3)
  else if shape = 7 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/nan/y-{tag}" (.num x) .nan, rng3)
  else if shape = 8 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else if shape = 9 then
    let (x, rng3) := pickSigned257ish rng2
    (mkCase s!"fuzz/underflow/one-int-{tag}" #[intV x], rng3)
  else if shape = 10 then
    let (x, rng3) := pickSigned257ish rng2
    let (nonInt, rng4) := pickQXorNonInt rng3
    (mkCase s!"fuzz/type/pop-y-first-non-int-{tag}" #[intV x, nonInt], rng4)
  else if shape = 11 then
    let (x, rng3) := pickSigned257ish rng2
    let (nonInt, rng4) := pickQXorNonInt rng3
    (mkCase s!"fuzz/type/pop-x-second-non-int-{tag}" #[nonInt, intV x], rng4)
  else
    let (x, rng3) := pickQXorOutOfRange rng2
    let (y, rng4) := pickSigned257ish rng3
    (mkInputCase s!"fuzz/range/pushint-out-of-range-{tag}" (.num x) (.num y), rng4)

def suite : InstrSuite where
  id := qxorId
  unit := #[
    { name := "unit/direct/twos-complement-identities"
      run := do
        let checks : Array (Int × Int × Int) :=
          #[
            (0, 0, 0),
            (7, 0, 7),
            (-7, 0, -7),
            (7, 7, 0),
            (-7, -7, 0),
            (7, -1, -8),
            (-7, -1, 6),
            (-5, 3, -8),
            (-7, -3, 4),
            (maxInt257, -1, minInt257),
            (minInt257, -1, maxInt257),
            (minInt257, maxInt257, -1)
          ]
        for c in checks do
          let x := c.1
          let y := c.2.1
          let expected := c.2.2
          expectOkStack s!"{x} qxor {y}" (runQXorDirect #[intV x, intV y]) #[intV expected] }
    ,
    { name := "unit/direct/error-order-underflow-before-type"
      run := do
        expectErr "underflow/empty" (runQXorDirect #[]) .stkUnd
        expectErr "underflow/one-int" (runQXorDirect #[intV 1]) .stkUnd
        expectErr "underflow/one-non-int" (runQXorDirect #[.null]) .stkUnd
        expectErr "type/pop-y-first-null" (runQXorDirect #[intV 1, .null]) .typeChk
        expectErr "type/pop-x-second-null" (runQXorDirect #[.null, intV 1]) .typeChk
        expectErr "error-order/both-non-int-pop-y-first"
          (runQXorDirect #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/quiet-nan-and-stack-selection"
      run := do
        expectOkStack "nan/x-propagates" (runQXorDirect #[.int .nan, intV 1]) #[.int .nan]
        expectOkStack "nan/y-propagates" (runQXorDirect #[intV 1, .int .nan]) #[.int .nan]
        expectOkStack "top-two-only-preserve-lower"
          (runQXorDirect #[.null, intV 7, intV 3]) #[.null, intV 4] }
    ,
    { name := "unit/dispatch/non-qxor-falls-through"
      run := do
        expectOkStack "fallback/non-contExt"
          (runQXorDispatchFallback .add #[]) #[intV 31337]
        expectOkStack "fallback/other-contExt"
          (runQXorDispatchFallback (.contExt .condSel) #[]) #[intV 31337] }
  ]
  oracle := #[
    mkInputCase "ok/zero/zero-zero" (.num 0) (.num 0),
    mkInputCase "ok/identity/right-zero" (.num 222) (.num 0),
    mkInputCase "ok/identity/left-zero" (.num 0) (.num 222),
    mkInputCase "ok/identity/self-positive" (.num 12345) (.num 12345),
    mkInputCase "ok/identity/self-negative" (.num (-12345)) (.num (-12345)),
    mkInputCase "ok/negone/with-positive" (.num 123) (.num (-1)),
    mkInputCase "ok/negone/with-negative" (.num (-123)) (.num (-1)),
    mkInputCase "ok/sign/mixed-sign" (.num (-5)) (.num 3),
    mkInputCase "ok/sign/both-negative" (.num (-7)) (.num (-3)),
    mkInputCase "boundary/min-xor-max" (.num minInt257) (.num maxInt257),
    mkInputCase "boundary/max-xor-neg-one" (.num maxInt257) (.num (-1)),
    mkInputCase "boundary/min-xor-neg-one" (.num minInt257) (.num (-1)),
    mkInputCase "boundary/high-bit-pair" (.num (pow2 255)) (.num (pow2 254)),
    mkInputCase "boundary/max-xor-high-bit" (.num maxInt257) (.num (pow2 255)),
    mkInputCase "boundary/min-xor-high-bit" (.num minInt257) (.num (pow2 255)),
    mkCase "underflow/empty" #[],
    mkCase "underflow/one-int" #[intV 1],
    mkCase "error-order/one-non-int-underflow-first" #[.null],
    mkCase "type/pop-y-first-null" #[intV 1, .null],
    mkCase "type/pop-x-second-null" #[.null, intV 1],
    mkCase "type/pop-y-first-cell" #[intV 1, .cell Cell.empty],
    mkCase "type/pop-x-second-cell" #[.cell Cell.empty, intV 1],
    mkCase "error-order/both-non-int-pop-y-first" #[.cell Cell.empty, .null],
    mkInputCase "nan/y-via-pushnan" (.num 42) .nan,
    mkInputCase "nan/x-via-pushnan" .nan (.num 42),
    mkInputCase "range/pushint-high-before-qxor" (.num (maxInt257 + 1)) (.num 1),
    mkInputCase "range/pushint-low-before-qxor" (.num (minInt257 - 1)) (.num 1),
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5]
      #[.pushInt (.num qxorSetGasExact), .tonEnvOp .setGasLimit, qxorInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5]
      #[.pushInt (.num qxorSetGasExactMinusOne), .tonEnvOp .setGasLimit, qxorInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 500
      gen := genQXorFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QXOR
