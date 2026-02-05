-- Auto-generated stub for TVM instruction LSHIFT_VAR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testLshiftVar : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 5), .lshift ])
  expectExitOk "lshift_var(1,5)" exitCode1
  assert (st1.stack.size == 1) s!"lshift_var(1,5): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 32) s!"lshift_var(1,5): expected 32, got {n}"
  | v => throw (IO.userError s!"lshift_var(1,5): unexpected stack value {v.pretty}")

  let (exitCodeNeg, _) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num (-1)), .lshift ])
  expectExitExc "lshift_var(1,-1)" .rangeChk exitCodeNeg

  let (exitCodeOv, _) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 256), .lshift ])
  expectExitExc "lshift_var(1,256)" .intOv exitCodeOv

initialize
  Tests.registerTest "arith/lshift_var" testLshiftVar
  Tests.registerRoundtrip (.lshift)
