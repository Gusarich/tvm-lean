import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.DIV

/-
DIV branch map (analyzed sources):

- Lean: `TvmLean/Semantics/Exec/Arith/DivMod.lean` (`execInstrArithDivMod`)
  - 2 outer dispatch arms (`.divMod` / fallthrough).
  - Inside `.divMod`: 6 branch sites, 14 outcomes total:
    - `addMode` pop path (2), operand-shape match (2), divisor-zero check (2),
      round-mode validity check (2), `d` switch (4), non-num `d==3` split (2).
  - DIV fixes parameters to `d=1`, `roundMode=-1`, `addMode=false`.

- C++ reference: `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
  - `exec_divmod`: 4 main branch sites, 10 outcomes:
    - add-mode remap gate (2), invalid-opcode guard (2),
      underflow guard (2), add/non-add execution split + `d` switch (4).
  - Opcode mapping for DIV family is under `register_div_ops` (`0xa90` + args4),
    with DIV using args4=`0x4` (`d=1`, floor mode), and quiet variant in `0xb7a90`.

Key risk areas covered by this suite:
- division-by-zero behavior (NaN result, not throw);
- stack underflow and type-check order (`y` pops before `x`);
- NaN operand propagation;
- signed floor semantics across sign combinations;
- 257-bit boundary overflow on result push (`-2^256 / -1`);
- low-gas out-of-gas behavior (pre-exec and implicit-RET boundary).
-/

private def divId : InstrId := { name := "DIV" }

private def divInstr : Instr := .divMod 1 (-1) false false

private def divProgram : Array Instr := #[divInstr]

private def divGasForInstr (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def divGasToHalt : Int :=
  divGasForInstr divInstr + implicitRetGasPrice

private def divSetGasNeed (n : Int) : Int :=
  divGasForInstr (.pushInt (.num n))
    + divGasForInstr (.tonEnvOp .setGasLimit)
    + divGasForInstr divInstr
    + implicitRetGasPrice

private def divSetGasFixedPoint (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := divSetGasNeed n
      if n' = n then n else divSetGasFixedPoint n' k

private def divSetGasExact : Int :=
  divSetGasFixedPoint 64 16

private def divSetGasExactMinusOne : Int :=
  if divSetGasExact > 0 then divSetGasExact - 1 else 0

private def vi (n : Int) : Value := .int (.num n)

private def mkDivOracle (name : String) (initStack : Array Value)
    (program : Array Instr := divProgram)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := divId
    program := program
    initStack := initStack
    gasLimits := gasLimits
    fuel := fuel }

private def failUnit (msg : String) : IO α :=
  throw (IO.userError msg)

private def divCodeIO : IO Cell := do
  match assembleCp0 divProgram.toList with
  | .ok code => pure code
  | .error e => failUnit s!"assemble DIV failed: {e}"

private def runDivLean (initStack : Array Value)
    (gasLimit : Int := 1_000_000) (gasMax : Int := 1_000_000)
    (fuel : Nat := 200_000) : IO StepResult := do
  let code ← divCodeIO
  let st0 := { (VmState.initial code gasLimit gasMax 0) with stack := initStack }
  pure (VmState.run nativeHost fuel st0)

private def expectExit (label : String) (expected : Int) (res : StepResult) : IO VmState := do
  match res with
  | .halt exitCode st =>
      if exitCode = expected then
        pure st
      else
        failUnit s!"{label}: expected exit={expected}, got {exitCode}"
  | .continue _ =>
      failUnit s!"{label}: execution did not halt"

private def expectTopIntNum (label : String) (expected : Int) (st : VmState) : IO Unit := do
  match st.stack.back? with
  | some (.int (.num n)) =>
      if n = expected then
        pure ()
      else
        failUnit s!"{label}: expected top int {expected}, got {n}"
  | some v =>
      failUnit s!"{label}: expected top int, got {reprStr v}"
  | none =>
      failUnit s!"{label}: expected non-empty stack"

private def pickIntWeighted (g : StdGen) : Int × StdGen :=
  pickSigned257ish g

private def pickNonZeroInt (g : StdGen) : Int × StdGen :=
  let (v, g') := pickIntWeighted g
  (if v = 0 then 1 else v, g')

private def divFuzzGen (g0 : StdGen) : OracleCase × StdGen :=
  let (bucket, g1) := randNat g0 0 99
  let (x, g2) := pickIntWeighted g1
  let (ynz, g3) := pickNonZeroInt g2
  let (tag, g4) := randNat g3 0 999_999
  let y := if bucket < 90 then ynz else (0 : Int)
  let kind := if y = 0 then "zero" else "nonzero"
  (mkDivOracle s!"fuzz/{kind}-{tag}" #[vi x, vi y], g4)

def suite : InstrSuite where
  id := { name := "DIV" }
  unit := #[
    { name := "unit/floor-sign-mix"
      run := do
        let res ← runDivLean #[vi (-7), vi 3]
        let st ← expectExit "unit/floor-sign-mix" (~~~ 0) res
        expectTopIntNum "unit/floor-sign-mix" (-3) st },
    { name := "unit/nan-operand-intov"
      run := do
        let res ← runDivLean #[vi 5, .int .nan]
        let _ ← expectExit "unit/nan-operand-intov" (~~~ Excno.intOv.toInt) res
        pure () },
    { name := "unit/overflow-min-div-neg1"
      run := do
        let res ← runDivLean #[vi minInt257, vi (-1)]
        let _ ← expectExit "unit/overflow-min-div-neg1" (~~~ Excno.intOv.toInt) res
        pure () },
    { name := "unit/gas-exact-halts"
      run := do
        let res ← runDivLean #[vi 7, vi 3] divGasToHalt divGasToHalt
        let st ← expectExit "unit/gas-exact-halts" (~~~ 0) res
        expectTopIntNum "unit/gas-exact-halts" 2 st },
    { name := "unit/gas-one-less-out-of-gas"
      run := do
        let res ← runDivLean #[vi 7, vi 3] (divGasToHalt - 1) (divGasToHalt - 1) 50
        let _ ← expectExit "unit/gas-one-less-out-of-gas" Excno.outOfGas.toInt res
        pure () },
    { name := "unit/gas-zero-out-of-gas"
      run := do
        let res ← runDivLean #[vi 7, vi 3] 0 0 50
        let _ ← expectExit "unit/gas-zero-out-of-gas" Excno.outOfGas.toInt res
        pure () }
  ]
  oracle := #[
    mkDivOracle "floor/pos-pos-inexact" #[vi 7, vi 3],
    mkDivOracle "floor/neg-pos-inexact" #[vi (-7), vi 3],
    mkDivOracle "floor/pos-neg-inexact" #[vi 7, vi (-3)],
    mkDivOracle "floor/neg-neg-inexact" #[vi (-7), vi (-3)],
    mkDivOracle "floor/neg-pos-small" #[vi (-1), vi 2],
    mkDivOracle "floor/pos-neg-small" #[vi 1, vi (-2)],
    mkDivOracle "floor/neg-pos-half" #[vi (-5), vi 2],
    mkDivOracle "floor/pos-neg-half" #[vi 5, vi (-2)],
    mkDivOracle "exact/pos-pos" #[vi 42, vi 7],
    mkDivOracle "exact/neg-pos" #[vi (-42), vi 7],
    mkDivOracle "exact/pos-neg" #[vi 42, vi (-7)],
    mkDivOracle "exact/neg-neg" #[vi (-42), vi (-7)],
    mkDivOracle "exact/zero-numerator" #[vi 0, vi 5],
    mkDivOracle "divzero/nonzero-over-zero" #[vi 5, vi 0],
    mkDivOracle "nan/x-via-program" #[vi 3] (program := #[.pushInt .nan, .xchg0 1, divInstr]),
    mkDivOracle "nan/y-via-program" #[vi 5] (program := #[.pushInt .nan, divInstr]),
    mkDivOracle "underflow/empty-stack" #[],
    mkDivOracle "underflow/missing-x-after-y-pop" #[vi 1],
    mkDivOracle "type/y-non-int-top" #[vi 1, .null],
    mkDivOracle "type/x-non-int-second" #[.null, vi 1],
    mkDivOracle "type/error-order-both-non-int" #[.cell Cell.empty, .null],
    mkDivOracle "boundary/max-div-one" #[vi maxInt257, vi 1],
    mkDivOracle "boundary/max-div-neg1" #[vi maxInt257, vi (-1)],
    mkDivOracle "boundary/min-div-one" #[vi minInt257, vi 1],
    mkDivOracle "overflow/min-div-neg1" #[vi minInt257, vi (-1)],
    mkDivOracle "gas/program-exact-succeeds" #[vi 7, vi 3]
      #[.pushInt (.num divSetGasExact), .tonEnvOp .setGasLimit, divInstr],
    mkDivOracle "gas/program-exact-minus-one-out-of-gas" #[vi 7, vi 3]
      #[.pushInt (.num divSetGasExactMinusOne), .tonEnvOp .setGasLimit, divInstr]
  ]
  fuzz := #[
    { seed := 2026020801
      count := 500
      gen := divFuzzGen }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.DIV
