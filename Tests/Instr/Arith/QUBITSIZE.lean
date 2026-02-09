import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QUBITSIZE

/-
QUBITSIZE branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Ubitsize.lean`
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp` (`exec_bitsize`, opcode wiring in
    `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp` (`AnyIntView::bit_size_any`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.hpp` + `stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite:
- Lean: 6 branch points / 8 terminal outcomes in `execInstrArithUbitsize`
  (opcode dispatch; `popInt` underflow/type/success; NaN-vs-num split; quiet gate for NaN;
   sign check for numeric input; quiet gate for negative numbers).
- QUBITSIZE path (`quiet=true`) reachable outcomes: success-width, success-NaN (from NaN),
  success-NaN (from negative input), `stkUnd`, `typeChk`.
- C++ (`exec_bitsize` with `sgnd=false`, `quiet=true`) aligned reachable outcomes:
  width success, quiet-NaN sentinel path, `stk_und`, `type_chk`.

Key risk areas:
- Quiet path must return NaN for NaN/negative input (must not throw `rangeChk`).
- Unsigned width edges (`0 -> 0`, powers of two, `maxInt257 -> 256`).
- Unary pop/error ordering: top non-int must fail before reading deeper stack values.
- Exact gas cliff for `PUSHINT n; SETGASLIMIT; QUBITSIZE` (exact vs exact-minus-one budget).
-/

private def qubitsizeId : InstrId := { name := "QUBITSIZE" }

private def qubitsizeInstr : Instr := .ubitsize true

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qubitsizeInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qubitsizeId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runQubitsizeDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithUbitsize qubitsizeInstr stack

private def runQubitsizeDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithUbitsize .add (VM.push (intV 777)) stack

private def qubitsizeSetGasExact : Int :=
  computeExactGasBudget qubitsizeInstr

private def qubitsizeSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qubitsizeInstr

private def toInRangeNonNegative (x : Int) : Int :=
  if x < 0 then
    if x = minInt257 then maxInt257 else -x
  else
    x

private def toInRangeNegative (x : Int) : Int :=
  if x < 0 then x else if x = 0 then -1 else -x

private def genQubitsizeFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
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
    (mkCase s!"fuzz/quiet/negative-boundary-to-nan-{tag}" #[intV x], r3)
  else if shape = 3 then
    let (x0, r2) := pickSigned257ish rng1
    let x := toInRangeNegative x0
    let (tag, r3) := randNat r2 0 999_999
    (mkCase s!"fuzz/quiet/negative-random-to-nan-{tag}" #[intV x], r3)
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
    (mkCase s!"fuzz/quiet/nan-via-program-{tag}" #[intV x] #[.pushInt .nan, qubitsizeInstr], r3)

def suite : InstrSuite where
  id := qubitsizeId
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
          expectOkStack s!"qubitsize {x}" (runQubitsizeDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/quiet/nan-and-negative-to-nan"
      run := do
        expectOkStack "nan-input" (runQubitsizeDirect #[.int .nan]) #[.int .nan]
        expectOkStack "negative-one" (runQubitsizeDirect #[intV (-1)]) #[.int .nan]
        expectOkStack "min-int257" (runQubitsizeDirect #[intV minInt257]) #[.int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-top-pop"
      run := do
        expectErr "empty-underflow" (runQubitsizeDirect #[]) .stkUnd
        expectErr "top-null" (runQubitsizeDirect #[.null]) .typeChk
        expectErr "top-cell" (runQubitsizeDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runQubitsizeDirect #[intV 9, .null]) .typeChk
        expectOkStack "top-int-below-non-int-untouched"
          (runQubitsizeDirect #[.null, intV 9]) #[.null, intV 4] }
    ,
    { name := "unit/dispatch/non-ubitsize-falls-through"
      run := do
        expectOkStack "dispatch/fallback" (runQubitsizeDispatchFallback #[]) #[intV 777] }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/one" #[intV 1],
    mkCase "ok/pow2-32" #[intV (pow2 32)],
    mkCase "ok/pow2-255" #[intV (pow2 255)],
    mkCase "ok/max-int257" #[intV maxInt257],
    mkCase "ok/top-order/below-kept" #[.null, intV 9],
    mkCase "quiet/negative-one-to-nan" #[intV (-1)],
    mkCase "quiet/min-int257-to-nan" #[intV minInt257],
    mkCase "quiet/nan-via-program" #[intV 42] #[.pushInt .nan, qubitsizeInstr],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-below-int" #[intV 9, .null],
    mkCase "error-order/top-int-below-non-int-untouched" #[.null, intV 9],
    mkCase "error-order/both-non-int-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV 7]
      #[.pushInt (.num qubitsizeSetGasExact), .tonEnvOp .setGasLimit, qubitsizeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7]
      #[.pushInt (.num qubitsizeSetGasExactMinusOne), .tonEnvOp .setGasLimit, qubitsizeInstr]
  ]
  fuzz := #[
    { seed := 2026020805
      count := 500
      gen := genQubitsizeFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QUBITSIZE
