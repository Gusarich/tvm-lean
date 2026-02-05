-- Auto-generated stub for TVM instruction QMODC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQmodc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 2 1 false true ])
  expectExitOk "qmodc(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmodc(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qmodc(-7,3): expected -1, got {n}"
  | v => throw (IO.userError s!"qmodc(-7,3): unexpected stack value {v.pretty}")

  let (exitCodeB, stB) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 2 1 false true ])
  expectExitOk "qmodc(minInt257,-1)" exitCodeB
  assert (stB.stack.size == 1) s!"qmodc(minInt257,-1): unexpected stack size={stB.stack.size}"
  match stB.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qmodc(minInt257,-1): expected 0, got {n}"
  | v => throw (IO.userError s!"qmodc(minInt257,-1): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qmodc" testQmodc
  Tests.registerRoundtrip (.divMod 2 1 false true)
