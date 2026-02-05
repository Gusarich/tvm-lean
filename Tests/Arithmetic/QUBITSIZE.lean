-- Auto-generated stub for TVM instruction QUBITSIZE (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQubitsize : IO Unit := do
  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .ubitsize true ])
  expectExitOk "qubitsize(0)" exitCode0
  assert (st0.stack.size == 1) s!"qubitsize(0): unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qubitsize(0): expected 0, got {n}"
  | v => throw (IO.userError s!"qubitsize(0): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .ubitsize true ])
  expectExitOk "qubitsize(nan)" exitCodeNan
  assert (stNan.stack.size == 1) s!"qubitsize(nan): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qubitsize(nan): expected NaN, got {v.pretty}")

  let (exitCodeNeg, stNeg) ← expectHalt (← runProg [ .pushInt (.num (-1)), .ubitsize true ])
  expectExitOk "qubitsize(-1)" exitCodeNeg
  assert (stNeg.stack.size == 1) s!"qubitsize(-1): unexpected stack size={stNeg.stack.size}"
  match stNeg.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qubitsize(-1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qubitsize" testQubitsize
  Tests.registerRoundtrip (.ubitsize true)
