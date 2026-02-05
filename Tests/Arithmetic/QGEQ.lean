-- Auto-generated stub for TVM instruction QGEQ (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQgeq : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 8), .contExt .qgeq ])
  expectExitOk "qgeq(8,8)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qgeq(8,8): expected -1, got {n}"
  | v => throw (IO.userError s!"qgeq(8,8): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 8), .contExt .qgeq ])
  expectExitOk "qgeq(7,8)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qgeq(7,8): expected 0, got {n}"
  | v => throw (IO.userError s!"qgeq(7,8): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qgeq" testQgeq
  Tests.registerRoundtrip (.contExt .qgeq)
