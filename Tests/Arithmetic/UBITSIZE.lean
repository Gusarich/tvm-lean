-- Auto-generated stub for TVM instruction UBITSIZE (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testUbitsize : IO Unit := do
  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .ubitsize false ])
  expectExitOk "ubitsize(0)" exitCode0
  assert (st0.stack.size == 1) s!"ubitsize(0): unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"ubitsize(0): expected 0, got {n}"
  | v => throw (IO.userError s!"ubitsize(0): unexpected stack value {v.pretty}")

  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num 1), .ubitsize false ])
  expectExitOk "ubitsize(1)" exitCode1
  assert (st1.stack.size == 1) s!"ubitsize(1): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"ubitsize(1): expected 1, got {n}"
  | v => throw (IO.userError s!"ubitsize(1): unexpected stack value {v.pretty}")

  let (exitCodeNeg, _) ← expectHalt (← runProg [ .pushInt (.num (-1)), .ubitsize false ])
  expectExitExc "ubitsize(-1)" .rangeChk exitCodeNeg

  let (exitCodeNan, _) ← expectHalt (← runProg [ .pushInt .nan, .ubitsize false ])
  expectExitExc "ubitsize(nan)" .rangeChk exitCodeNan

initialize
  Tests.registerTest "arith/ubitsize" testUbitsize
  Tests.registerRoundtrip (.ubitsize false)
