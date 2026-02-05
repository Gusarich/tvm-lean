-- Auto-generated stub for TVM instruction QMULDIV (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def bigMulA : Int :=
  pow2 200

private def bigMulB : Int :=
  pow2 100

def testQmuldiv : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-5)), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 1 (-1) false true ])
  expectExitOk "qmuldiv(-5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmuldiv(-5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -7) s!"qmuldiv(-5,4,3): expected -7, got {n}"
  | v => throw (IO.userError s!"qmuldiv(-5,4,3): unexpected stack value {v.pretty}")

  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num bigMulA), .pushInt (.num bigMulB), .pushInt (.num 1), .mulDivMod 1 (-1) false true ])
  expectExitOk "qmuldiv(2^200,2^100,1)" exitCodeOv
  assert (stOv.stack.size == 1) s!"qmuldiv(2^200,2^100,1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qmuldiv(2^200,2^100,1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qmuldiv" testQmuldiv
  Tests.registerRoundtrip (.mulDivMod 1 (-1) false true)
