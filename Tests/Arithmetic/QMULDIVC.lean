-- Auto-generated stub for TVM instruction QMULDIVC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQmuldivc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-5)), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 1 1 false true ])
  expectExitOk "qmuldivc(-5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"qmuldivc(-5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -6) s!"qmuldivc(-5,4,3): expected -6, got {n}"
  | v => throw (IO.userError s!"qmuldivc(-5,4,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qmuldivc" testQmuldivc
  Tests.registerRoundtrip (.mulDivMod 1 1 false true)
