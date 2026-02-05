-- Auto-generated stub for TVM instruction QEQUAL (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQequal : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 7), .contExt .qequal ])
  expectExitOk "qequal(7,7)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qequal(7,7): expected -1, got {n}"
  | v => throw (IO.userError s!"qequal(7,7): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 8), .contExt .qequal ])
  expectExitOk "qequal(7,8)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qequal(7,8): expected 0, got {n}"
  | v => throw (IO.userError s!"qequal(7,8): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qequal" testQequal
  Tests.registerRoundtrip (.contExt .qequal)
