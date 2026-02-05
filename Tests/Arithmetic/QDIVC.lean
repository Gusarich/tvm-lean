-- Auto-generated stub for TVM instruction QDIVC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQdivc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 1 1 false true ])
  expectExitOk "qdivc(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"qdivc(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"qdivc(-7,3): expected -2, got {n}"
  | v => throw (IO.userError s!"qdivc(-7,3): unexpected stack value {v.pretty}")

  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 1 1 false true ])
  expectExitOk "qdivc(minInt257,-1)" exitCodeOv
  assert (stOv.stack.size == 1) s!"qdivc(minInt257,-1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qdivc(minInt257,-1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qdivc" testQdivc
  Tests.registerRoundtrip (.divMod 1 1 false true)
