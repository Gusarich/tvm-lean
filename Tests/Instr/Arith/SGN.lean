import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.SGN

/-
SGN branch-mapping notes (Lean + C++ reference):
- Lean analyzed file: `TvmLean/Semantics/Exec/Arith/Sgn.lean`
- C++ analyzed file: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  (`exec_sgn`, opcode registration in `register_int_cmp_ops`).

Branch map used by this suite:
- Lean: 5 branch points / 7 terminal outcomes
  (opcode dispatch; `popInt` success-vs-error; NaN-vs-num split;
   numeric sign split `<0`, `=0`, `>0`; and non-quiet NaN `pushIntQuiet` throw path).
- C++: 5 branch points / 7 aligned terminal outcomes
  (`SGN` registration binds `exec_sgn(..., mode=0x987, quiet=false)`;
   underflow guard; `pop_int` type check; invalid-vs-valid int branch;
   `td::sgn` mapping across negative/zero/positive outcomes).

Key divergence risk areas:
- Mode-table decoding (`0x987`) must map exactly to `-1/0/1`.
- NaN handling in non-quiet SGN must throw (`intOv`) rather than return NaN.
- Error ordering must remain underflow-first, then type-check on top value.
- Boundary and near-boundary finite inputs must still return smallints (no overflow).
- Gas-boundary behavior should be deterministic for exact and exact-minus-one budgets.
-/

private def sgnId : InstrId := { name := "SGN" }

private def intV (n : Int) : Value :=
  .int (.num n)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[.sgn])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sgnId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSgnDirect (stack : Array Value) : Except Excno (Array Value) :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (execInstrArithSgn .sgn (pure ())).run st0
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

private def expectOkStack (label : String) (res : Except Excno (Array Value)) (expected : Array Value) : IO Unit := do
  match res with
  | .ok st =>
      if st == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

private def expectErr (label : String) (res : Except Excno (Array Value)) (expected : Excno) : IO Unit := do
  match res with
  | .ok st =>
      throw (IO.userError s!"{label}: expected error {expected}, got stack {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def sgnGasForInstr (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def sgnSetGasNeed (n : Int) : Int :=
  sgnGasForInstr (.pushInt (.num n))
    + sgnGasForInstr (.tonEnvOp .setGasLimit)
    + sgnGasForInstr .sgn
    + implicitRetGasPrice

private def sgnSetGasFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := sgnSetGasNeed n
      if n' = n then n else sgnSetGasFixedPoint n' k

private def sgnSetGasExact : Int :=
  sgnSetGasFixedPoint 64 16

private def sgnSetGasExactMinusOne : Int :=
  if sgnSetGasExact > 0 then sgnSetGasExact - 1 else 0

private def genSgnFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 4
  let (x, rng2) :=
    if shape = 0 then
      pickInt257Boundary rng1
    else if shape = 1 then
      pickSigned257ish rng1
    else if shape = 2 then
      let (b, r2) := pickInt257Boundary rng1
      let (dir, r3) := randNat r2 0 1
      let x' :=
        if b = minInt257 then minInt257 + 1
        else if b = maxInt257 then maxInt257 - 1
        else if dir = 0 then b - 1 else b + 1
      (x', r3)
    else if shape = 3 then
      let (idx, r2) := randNat rng1 0 2
      let x' : Int := if idx = 0 then -1 else if idx = 1 then 0 else 1
      (x', r2)
    else
      pickSigned257ish rng1
  (mkCase s!"fuzz/shape-{shape}" #[intV x], rng2)

def suite : InstrSuite where
  id := sgnId
  unit := #[
    { name := "unit/finite-sign-and-boundary-mapping"
      run := do
        let checks : Array (Int × Int) :=
          #[
            (-9, -1),
            (-1, -1),
            (0, 0),
            (1, 1),
            (9, 1),
            (minInt257, -1),
            (minInt257 + 1, -1),
            (maxInt257 - 1, 1),
            (maxInt257, 1)
          ]
        for c in checks do
          let input := c.1
          let expected := c.2
          expectOkStack s!"sgn({input})" (runSgnDirect #[intV input]) #[intV expected] }
    ,
    { name := "unit/nan-non-quiet-throws-intov"
      run := do
        expectErr "sgn(nan)" (runSgnDirect #[.int .nan]) .intOv }
    ,
    { name := "unit/type-check-on-non-int-top"
      run := do
        expectErr "null" (runSgnDirect #[.null]) .typeChk
        expectErr "cell" (runSgnDirect #[.cell Cell.empty]) .typeChk }
    ,
    { name := "unit/underflow-empty-stack"
      run := do
        expectErr "empty" (runSgnDirect #[]) .stkUnd }
  ]
  oracle := #[
    mkCase "ok/zero" #[intV 0],
    mkCase "ok/positive-small" #[intV 1],
    mkCase "ok/negative-small" #[intV (-1)],
    mkCase "ok/positive-large" #[intV (pow2 200)],
    mkCase "ok/negative-large" #[intV (-(pow2 200))],
    mkCase "boundary/min" #[intV minInt257],
    mkCase "boundary/min-plus-one-near" #[intV (minInt257 + 1)],
    mkCase "boundary/max-minus-one-near" #[intV (maxInt257 - 1)],
    mkCase "boundary/max" #[intV maxInt257],
    mkCase "underflow/empty-stack" #[],
    mkCase "type/top-null" #[.null],
    mkCase "type/top-cell" #[.cell Cell.empty],
    mkCase "overflow/nan-via-pushnan-program" #[] #[.pushInt .nan, .sgn],
    mkCase "gas/exact-cost-succeeds" #[intV (-7)]
      #[.pushInt (.num sgnSetGasExact), .tonEnvOp .setGasLimit, .sgn],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV (-7)]
      #[.pushInt (.num sgnSetGasExactMinusOne), .tonEnvOp .setGasLimit, .sgn]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := genSgnFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.SGN
