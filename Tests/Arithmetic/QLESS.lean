-- Auto-generated stub for TVM instruction QLESS (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQless : IO Unit := do
  let (exitCodeT, stT) ← expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 2), .contExt .qless ])
  expectExitOk "qless(1,2)" exitCodeT
  match stT.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qless(1,2): expected -1, got {n}"
  | v => throw (IO.userError s!"qless(1,2): unexpected stack value {v.pretty}")

  let (exitCodeF, stF) ← expectHalt (← runProg [ .pushInt (.num 2), .pushInt (.num 1), .contExt .qless ])
  expectExitOk "qless(2,1)" exitCodeF
  match stF.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qless(2,1): expected 0, got {n}"
  | v => throw (IO.userError s!"qless(2,1): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 1), .contExt .qless ])
  expectExitOk "qless(NaN,1)" exitCodeNan
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qless(NaN,1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qless" testQless
  Tests.registerRoundtrip (.contExt .qless)
