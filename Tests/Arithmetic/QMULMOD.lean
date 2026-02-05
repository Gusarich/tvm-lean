-- Auto-generated stub for TVM instruction QMULMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQmulmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 (-1) false true ])
  expectExitOk "qmulmod(5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmulmod(5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"qmulmod(5,4,3): expected 2, got {n}"
  | v => throw (IO.userError s!"qmulmod(5,4,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qmulmod" testQmulmod
  Tests.registerRoundtrip (.mulDivMod 2 (-1) false true)
