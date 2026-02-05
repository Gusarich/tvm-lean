-- Auto-generated stub for TVM instruction AND (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAnd : IO Unit := do
  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num (-1)), .pushInt (.num 15), .and_ ])
  expectExitOk "and(-1,15)" exitCode1
  assert (st1.stack.size == 1) s!"and(-1,15): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 15) s!"and(-1,15): expected 15, got {n}"
  | v => throw (IO.userError s!"and(-1,15): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 1), .and_ ])
  expectExitOk "and(nan,1)" exitCodeNan
  assert (stNan.stack.size == 1) s!"and(nan,1): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"and(nan,1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/and" testAnd
  Tests.registerRoundtrip (.and_)
