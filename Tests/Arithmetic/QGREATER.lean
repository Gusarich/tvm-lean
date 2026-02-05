-- Auto-generated stub for TVM instruction QGREATER (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQgreater : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 9), .pushInt (.num 8), .contExt .qgreater ])
  expectExitOk "qgreater(9,8)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qgreater(9,8): expected -1, got {n}"
  | v => throw (IO.userError s!"qgreater(9,8): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 8), .contExt .qgreater ])
  expectExitOk "qgreater(7,8)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qgreater(7,8): expected 0, got {n}"
  | v => throw (IO.userError s!"qgreater(7,8): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qgreater" testQgreater
  Tests.registerRoundtrip (.contExt .qgreater)
