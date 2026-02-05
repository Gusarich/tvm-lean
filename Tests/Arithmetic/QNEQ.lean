-- Auto-generated stub for TVM instruction QNEQ (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQneq : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 8), .contExt .qneq ])
  expectExitOk "qneq(7,8)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qneq(7,8): expected -1, got {n}"
  | v => throw (IO.userError s!"qneq(7,8): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 7), .contExt .qneq ])
  expectExitOk "qneq(7,7)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qneq(7,7): expected 0, got {n}"
  | v => throw (IO.userError s!"qneq(7,7): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qneq" testQneq
  Tests.registerRoundtrip (.contExt .qneq)
