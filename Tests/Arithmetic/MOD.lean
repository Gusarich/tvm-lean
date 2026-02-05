-- Auto-generated stub for TVM instruction MOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testMod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 2 (-1) false false ])
  expectExitOk "mod(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"mod(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"mod(-7,3): expected 2, got {n}"
  | v => throw (IO.userError s!"mod(-7,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num (-3)), .divMod 2 (-1) false false ])
  expectExitOk "mod(7,-3)" exitCode2
  assert (st2.stack.size == 1) s!"mod(7,-3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"mod(7,-3): expected -2, got {n}"
  | v => throw (IO.userError s!"mod(7,-3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 2 (-1) false false ])
  expectExitOk "mod(1,0)" exitCodeZ
  assert (stZ.stack.size == 1) s!"mod(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"mod(1,0): expected NaN, got {v.pretty}")

  -- Even when quotient would overflow (MIN_INT / -1), MOD returns 0.
  let (exitCodeB, stB) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 2 (-1) false false ])
  expectExitOk "mod(minInt257,-1)" exitCodeB
  assert (stB.stack.size == 1) s!"mod(minInt257,-1): unexpected stack size={stB.stack.size}"
  match stB.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"mod(minInt257,-1): expected 0, got {n}"
  | v => throw (IO.userError s!"mod(minInt257,-1): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/mod" testMod
  Tests.registerRoundtrip (.divMod 2 (-1) false false)
