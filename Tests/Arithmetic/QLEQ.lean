-- Auto-generated stub for TVM instruction QLEQ (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQleq : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 8), .contExt .qleq ])
  expectExitOk "qleq(7,8)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qleq(7,8): expected -1, got {n}"
  | v => throw (IO.userError s!"qleq(7,8): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 9), .pushInt (.num 8), .contExt .qleq ])
  expectExitOk "qleq(9,8)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qleq(9,8): expected 0, got {n}"
  | v => throw (IO.userError s!"qleq(9,8): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qleq" testQleq
  Tests.registerRoundtrip (.contExt .qleq)
