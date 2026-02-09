import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.UBITSIZE

/-
UBITSIZE branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ubitsize.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_bitsize`, opcode wiring in
    `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp` (`AnyIntView::bit_size_any`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`check_underflow`, `pop_int`)

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes in `execInstrArithUbitsize`
  (opcode dispatch; `popInt` underflow/type/success; NaN-vs-num split; quiet gate for NaN;
   sign check for numeric input; quiet gate for negative numbers).
- UBITSIZE path (`quiet=false`) reachable outcomes: success, `stkUnd`, `typeChk`,
  `rangeChk` on NaN, `rangeChk` on negative input.
- C++ (`exec_bitsize` with `sgnd=false`, `quiet=false`): 4 branch points / 5 aligned outcomes
  (underflow check; `pop_int` type check; `bit_size(false)` valid-vs-sentinel; non-quiet
   sentinel path throws `range_chk`).

Key risk areas:
- NaN and negative operands must throw `rangeChk` (not `intOv`) in non-quiet UBITSIZE.
- Unsigned width edge cases (`0 -> 0`, powers of two, `maxInt257 -> 256`).
- Unary pop/error ordering: top non-int must fail even when lower entries are valid ints.
- Exact gas cliff for `PUSHINT n; SETGASLIMIT; UBITSIZE` (exact vs exact-minus-one budget).
-/

private def ubitsizeId : InstrId := { name := "UBITSIZE" }

private def ubitsizeInstr : Instr := .ubitsize false

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ubitsizeInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ubitsizeId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runUbitsizeDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithUbitsize ubitsizeInstr stack

private def runUbitsizeDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithUbitsize .add (VM.push (intV 777)) stack

private def ubitsizeSetGasExact : Int :=
  computeExactGasBudget ubitsizeInstr

private def ubitsizeSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ubitsizeInstr

private def toInRangeNonNegative (x : Int) : Int :=
  if x < 0 then
    if x = minInt257 then maxInt257 else -x
  else
    x

private def toInRangeNegative (x : Int) : Int :=
  if x < 0 then x else if x = 0 then -1 else -x

private def genUbitsizeFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 8
  if shape = 0 then
    let (x0, r2) := pickInt257Boundary rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/ok/boundary-{tag}" #[intV x], r3)
  else if shape = 1 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/ok/random-nonnegative-{tag}" #[intV x], r3)
  else if shape = 2 then
    let (x0, r2) := pickInt257Boundary rng1
    let x := toInRangeNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/range/negative-boundary-{tag}" #[intV x], r3)
  else if shape = 3 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/range/negative-random-{tag}" #[intV x], r3)
  else if shape = 4 then
    let (tag, r2) := randNat rng1 0 999_999
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], r2)
  else if shape = 5 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/type/top-null-{tag}" #[intV x, .null], r3)
  else if shape = 6 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/error-order/top-non-int-before-below-int-{tag}" #[intV x, .cell Cell.empty], r3)
  else if shape = 7 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/error-order/top-int-below-non-int-untouched-{tag}" #[.null, intV x], r3)
  else
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNonNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/range/nan-via-program-{tag}" #[intV x] #[.pushInt .nan, ubitsizeInstr], r3)

def suite : InstrSuite where
  id := ubitsizeId
  unit := #[
    { name := "unit/ok/nonnegative-widths"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (0, 0),
            (1, 1),
            (2, 2),
            (3, 2),
            (7, 3),
            (8, 4),
            (pow2 32, 33),
            (pow2 255, 256),
            (maxInt257, 256)
          ]
        for c in checks do
          let x := c.1
          let expected := c.2
          expectOkStack s!"ubitsize {x}" (runUbitsizeDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/range/negative-throws-rangechk"
      run := do
        expectErr "negative-one" (runUbitsizeDirect #[intV (-1)]) .rangeChk
        expectErr "min-int257" (runUbitsizeDirect #[intV minInt257]) .rangeChk }
    ,
    { name := "unit/error-order/underflow-type-and-top-pop"
      run := do
        expectErr "empty-underflow" (runUbitsizeDirect #[]) .stkUnd
        expectErr "top-null" (runUbitsizeDirect #[.null]) .typeChk
        expectErr "top-cell" (runUbitsizeDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runUbitsizeDirect #[intV 9, .null]) .typeChk
        expectOkStack "top-int-below-non-int-untouched"
          (runUbitsizeDirect #[.null, intV 9]) #[.null, intV 4] }
    ,
    { name := "unit/dispatch/non-ubitsize-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runUbitsizeDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/one" #[intV 1],
    mkCase "ok/pow2-32" #[intV (pow2 32)],
    mkCase "ok/pow2-255" #[intV (pow2 255)],
    mkCase "ok/max-int257" #[intV maxInt257],
    mkCase "ok/top-order/below-kept" #[.null, intV 9],
    mkCase "range/negative-one" #[intV (-1)],
    mkCase "range/min-int257" #[intV minInt257],
    mkCase "range/nan-via-program" #[intV 42] #[.pushInt .nan, ubitsizeInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-below-int" #[intV 9, .null],
    mkCase "error-order/top-int-below-non-int-untouched" #[.null, intV 9],
    mkCase "error-order/both-non-int-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num ubitsizeSetGasExact), .tonEnvOp .setGasLimit, ubitsizeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num ubitsizeSetGasExactMinusOne), .tonEnvOp .setGasLimit, ubitsizeInstr]
  ]
  fuzz := #[
    { seed := 2026020804
      count := 500
      gen := genUbitsizeFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.UBITSIZE
