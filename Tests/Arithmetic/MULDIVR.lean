-- Auto-generated stub for TVM instruction MULDIVR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMuldivr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 1 0 false false ])
  expectExitOk "muldivr(5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"muldivr(5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 7) s!"muldivr(5,4,3): expected 7, got {n}"
  | v => throw (IO.userError s!"muldivr(5,4,3): unexpected stack value {v.pretty}")

  -- tie (0.5) rounds away from zero
  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 1), .pushInt (.num 2), .mulDivMod 1 0 false false ])
  expectExitOk "muldivr(1,1,2)" exitCode2
  assert (st2.stack.size == 1) s!"muldivr(1,1,2): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"muldivr(1,1,2): expected 1, got {n}"
  | v => throw (IO.userError s!"muldivr(1,1,2): unexpected stack value {v.pretty}")

  let (exitCode3, st3) ←
    expectHalt (← runProg [ .pushInt (.num (-1)), .pushInt (.num 1), .pushInt (.num 2), .mulDivMod 1 0 false false ])
  expectExitOk "muldivr(-1,1,2)" exitCode3
  assert (st3.stack.size == 1) s!"muldivr(-1,1,2): unexpected stack size={st3.stack.size}"
  match st3.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"muldivr(-1,1,2): expected -1, got {n}"
  | v => throw (IO.userError s!"muldivr(-1,1,2): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/muldivr" testMuldivr
  Tests.registerRoundtrip (.mulDivMod 1 0 false false)
