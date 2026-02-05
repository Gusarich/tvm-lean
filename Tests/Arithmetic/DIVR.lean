-- Auto-generated stub for TVM instruction DIVR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDivr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 1 0 false false ])
  expectExitOk "divr(8,3)" exitCode1
  assert (st1.stack.size == 1) s!"divr(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 3) s!"divr(8,3): expected 3, got {n}"
  | v => throw (IO.userError s!"divr(8,3): unexpected stack value {v.pretty}")

  -- tie (0.5) rounds away from zero
  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 3), .pushInt (.num 2), .divMod 1 0 false false ])
  expectExitOk "divr(3,2)" exitCode2
  assert (st2.stack.size == 1) s!"divr(3,2): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"divr(3,2): expected 2, got {n}"
  | v => throw (IO.userError s!"divr(3,2): unexpected stack value {v.pretty}")

  let (exitCode3, st3) ←
    expectHalt (← runProg [ .pushInt (.num (-3)), .pushInt (.num 2), .divMod 1 0 false false ])
  expectExitOk "divr(-3,2)" exitCode3
  assert (st3.stack.size == 1) s!"divr(-3,2): unexpected stack size={st3.stack.size}"
  match st3.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"divr(-3,2): expected -2, got {n}"
  | v => throw (IO.userError s!"divr(-3,2): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 1 0 false false ])
  expectExitOk "divr(1,0)" exitCodeZ
  assert (stZ.stack.size == 1) s!"divr(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"divr(1,0): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/divr" testDivr
  Tests.registerRoundtrip (.divMod 1 0 false false)
