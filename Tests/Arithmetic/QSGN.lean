-- Auto-generated stub for TVM instruction QSGN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQsgn : IO Unit := do
  let (exitCodeNeg, stNeg) ← expectHalt (← runProg [ .pushInt (.num (-7)), .contExt .qsgn ])
  expectExitOk "qsgn(-7)" exitCodeNeg
  match stNeg.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qsgn(-7): expected -1, got {n}"
  | v => throw (IO.userError s!"qsgn(-7): unexpected stack value {v.pretty}")

  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .contExt .qsgn ])
  expectExitOk "qsgn(0)" exitCode0
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qsgn(0): expected 0, got {n}"
  | v => throw (IO.userError s!"qsgn(0): unexpected stack value {v.pretty}")

  let (exitCodePos, stPos) ← expectHalt (← runProg [ .pushInt (.num 7), .contExt .qsgn ])
  expectExitOk "qsgn(7)" exitCodePos
  match stPos.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"qsgn(7): expected 1, got {n}"
  | v => throw (IO.userError s!"qsgn(7): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .contExt .qsgn ])
  expectExitOk "qsgn(NaN)" exitCodeNan
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qsgn(NaN): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qsgn" testQsgn
  Tests.registerRoundtrip (.contExt .qsgn)
