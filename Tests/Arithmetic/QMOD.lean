-- Auto-generated stub for TVM instruction QMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 2 (-1) false true ])
  expectExitOk "qmod(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmod(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"qmod(-7,3): expected 2, got {n}"
  | v => throw (IO.userError s!"qmod(-7,3): unexpected stack value {v.pretty}")

  let (exitCodeB, stB) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 2 (-1) false true ])
  expectExitOk "qmod(minInt257,-1)" exitCodeB
  assert (stB.stack.size == 1) s!"qmod(minInt257,-1): unexpected stack size={stB.stack.size}"
  match stB.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qmod(minInt257,-1): expected 0, got {n}"
  | v => throw (IO.userError s!"qmod(minInt257,-1): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qmod" testQmod
  Tests.registerRoundtrip (.divMod 2 (-1) false true)
