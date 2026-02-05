-- Auto-generated stub for TVM instruction QMULMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQmulmodr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 0 false true ])
  expectExitOk "qmulmodr(5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmulmodr(5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qmulmodr(5,4,3): expected -1, got {n}"
  | v => throw (IO.userError s!"qmulmodr(5,4,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qmulmodr" testQmulmodr
  Tests.registerRoundtrip (.mulDivMod 2 0 false true)
