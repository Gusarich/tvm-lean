import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QBITSIZE

/-
QBITSIZE branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/ContExt.lean` (`.qbitsize`, `signedBitsizeTvm`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `pushIntQuiet`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_bitsize`, opcode wiring in `register_shift_logic_ops`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`AnyIntView::bit_size_any`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_int`, `push_int_quiet`)

Branch map used for this suite:
- Lean: 6 branch points / 8 terminal outcomes
  (dispatch to `.contExt`; dispatch to `.qbitsize`; unary pop underflow/type/success;
   NaN-vs-num split; signed-width split `n = 0` vs `n ≠ 0`; nonzero split `n > 0` vs `n < 0`).
- C++: 5 branch points / 8 aligned terminal outcomes for QBITSIZE
  (underflow guard; `pop_int` type check; `bit_size(true)` finite-vs-sentinel;
   finite signed-width split on zero/positive/negative; quiet sentinel path pushes NaN).

Key risk areas:
- quiet-NaN semantics: QBITSIZE on NaN must return NaN (not `0`);
- signed-width off-by-one around `-1/0/1`, `±2^255`, `[-2^256, 2^256-1]`;
- unary pop ordering: `stkUnd` vs `typeChk`, and top-of-stack selection;
- program-ordering: `PUSHINT` out-of-range failure must occur before QBITSIZE;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QBITSIZE` (exact vs exact-minus-one).
-/

private def qbitsizeId : InstrId := { name := "QBITSIZE" }

private def qbitsizeInstr : Instr := .contExt .qbitsize

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qbitsizeInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qbitsizeId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (x : IntVal)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix.push qbitsizeInstr)

private def mkInputProgramCase
    (name : String)
    (x : IntVal)
    (programSuffix : Array Instr)
    (below : Array Value := #[]) : OracleCase :=
  let (stackOrEmpty, progPrefix) := oracleIntInputsToStackOrProgram #[x]
  mkCase name (below ++ stackOrEmpty) (progPrefix ++ programSuffix)

private def runQbitsizeDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithContExt qbitsizeInstr stack

private def runQbitsizeDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithContExt instr (VM.push (intV 777)) stack

private def qbitsizeSetGasExact : Int :=
  computeExactGasBudget qbitsizeInstr

private def qbitsizeSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qbitsizeInstr

private def qbitsizeBoundaryPool : Array Int :=
  #[
    0, 1, -1, 2, -2, 3, -3,
    (pow2 255) - 1, -(pow2 255), pow2 255, -(pow2 255) - 1,
    maxInt257, maxInt257 - 1, minInt257, minInt257 + 1
  ]

private def qbitsizeOutOfRangePool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257)
  ]

private def pickQbitsizeBoundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qbitsizeBoundaryPool.size - 1)
  (qbitsizeBoundaryPool[idx]!, rng')

private def pickQbitsizeOutOfRange (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (qbitsizeOutOfRangePool.size - 1)
  (qbitsizeOutOfRangePool[idx]!, rng')

private def pickQbitsizeNonInt (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 1
  ((if tag = 0 then .null else .cell Cell.empty), rng')

private def genQbitsizeFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  let (tag, rng2) := randNat rng1 0 999_999
  if shape = 0 then
    let (x, rng3) := pickQbitsizeBoundary rng2
    (mkInputCase s!"fuzz/ok/boundary-{tag}" (.num x), rng3)
  else if shape = 1 then
    let (x, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/ok/random-{tag}" (.num x), rng3)
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
    (mkInputCase s!"fuzz/ok/pow2-edge-{tag}" (.num x), rng4)
  else if shape = 3 then
    let (below, rng3) := pickSigned257ish rng2
    (mkInputCase s!"fuzz/nan/pushnan-over-int-{tag}" .nan #[intV below], rng3)
  else if shape = 4 then
    let (x, rng3) := pickQbitsizeOutOfRange rng2
    (mkInputCase s!"fuzz/error-order/pushint-out-of-range-before-qbitsize-{tag}" (.num x), rng3)
  else if shape = 5 then
    (mkCase s!"fuzz/underflow/empty-{tag}" #[], rng2)
  else if shape = 6 then
    let (top, rng3) := pickQbitsizeNonInt rng2
    (mkCase s!"fuzz/type/single-non-int-{tag}" #[top], rng3)
  else if shape = 7 then
    let (top, rng3) := pickQbitsizeNonInt rng2
    let (x, rng4) := pickSigned257ish rng3
    (mkCase s!"fuzz/type/top-non-int-before-below-int-{tag}" #[intV x, top], rng4)
  else if shape = 8 then
    let (top, rng3) := pickQbitsizeNonInt rng2
    let (x, rng4) := pickSigned257ish rng3
    (mkInputCase s!"fuzz/ok/top-int-below-non-int-{tag}" (.num x) #[top], rng4)
  else
    let (x, rng3) := pickSigned257ish rng2
    (mkInputProgramCase s!"fuzz/ok/double-qbitsize-{tag}" (.num x) #[qbitsizeInstr, qbitsizeInstr], rng3)

def suite : InstrSuite where
  id := qbitsizeId
  unit := #[
    { name := "unit/ok/known-signed-widths-and-boundaries"
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
          expectOkStack s!"qbitsize {x}" (runQbitsizeDirect #[intV x]) #[intV expected] }
    ,
    { name := "unit/nan/quiet-nan-regression"
      run := do
        expectOkStack "qbitsize/nan-single" (runQbitsizeDirect #[.int .nan]) #[.int .nan]
        expectOkStack "qbitsize/nan-over-int" (runQbitsizeDirect #[intV 42, .int .nan]) #[intV 42, .int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-top-pop"
      run := do
        expectErr "empty-underflow" (runQbitsizeDirect #[]) .stkUnd
        expectErr "top-null" (runQbitsizeDirect #[.null]) .typeChk
        expectErr "top-cell" (runQbitsizeDirect #[.cell Cell.empty]) .typeChk
        expectErr "top-non-int-before-below-int" (runQbitsizeDirect #[intV 9, .null]) .typeChk
        expectOkStack "top-int-below-non-int-untouched"
          (runQbitsizeDirect #[.null, intV (-7)])
          #[.null, intV 4] }
    ,
    { name := "unit/dispatch/non-qbitsize-falls-through"
      run := do
        expectOkStack "fallback/non-contExt"
          (runQbitsizeDispatchFallback .add #[]) #[intV 777]
        expectOkStack "fallback/other-contExt"
          (runQbitsizeDispatchFallback (.contExt .condSel) #[]) #[intV 777] }
  ]
  oracle := #[
    mkInputCase "ok/zero" (.num 0),
    mkInputCase "ok/positive-small" (.num 7),
    mkInputCase "ok/negative-small" (.num (-7)),
    mkInputCase "ok/positive-power-minus-one" (.num ((pow2 255) - 1)),
    mkInputCase "ok/negative-power" (.num (-(pow2 255))),
    mkInputCase "boundary/max-int257" (.num maxInt257),
    mkInputCase "boundary/max-minus-one" (.num (maxInt257 - 1)),
    mkInputCase "boundary/min-int257" (.num minInt257),
    mkInputCase "boundary/min-plus-one" (.num (minInt257 + 1)),
    mkInputProgramCase "ok/double-qbitsize" (.num 123456789) #[qbitsizeInstr, qbitsizeInstr],
    mkInputCase "ok/top-int-below-null" (.num 9) #[.null],
    mkInputCase "ok/top-int-below-cell" (.num (-9)) #[.cell Cell.empty],
    mkInputCase "nan/pushnan-empty" .nan,
    mkInputCase "nan/pushnan-over-int" .nan #[intV 42],
    mkInputCase "nan/pushnan-over-null" .nan #[.null],
    mkInputCase "error-order/pushint-out-of-range-before-qbitsize/positive" (.num (maxInt257 + 1)),
    mkInputCase "error-order/pushint-out-of-range-before-qbitsize/negative" (.num (minInt257 - 1)),
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "error-order/top-non-int-before-below-int" #[intV 9, .null],
    mkInputCase "error-order/top-int-below-non-int-untouched" (.num (-7)) #[.null],
    mkCase "error-order/both-non-int-top-first" #[.cell Cell.empty, .null],
    mkCase "gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num qbitsizeSetGasExact), .tonEnvOp .setGasLimit, qbitsizeInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num qbitsizeSetGasExactMinusOne), .tonEnvOp .setGasLimit, qbitsizeInstr]
  ]
  fuzz := #[
    { seed := 2026020815
      count := 500
      gen := genQbitsizeFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QBITSIZE
