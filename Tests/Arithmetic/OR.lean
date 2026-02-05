-- Auto-generated stub for TVM instruction OR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testOr : IO Unit := do
  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num 0), .pushInt (.num 5), .or ])
  expectExitOk "or(0,5)" exitCode1
  assert (st1.stack.size == 1) s!"or(0,5): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 5) s!"or(0,5): expected 5, got {n}"
  | v => throw (IO.userError s!"or(0,5): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt (.num 1), .pushInt .nan, .or ])
  expectExitOk "or(1,nan)" exitCodeNan
  assert (stNan.stack.size == 1) s!"or(1,nan): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"or(1,nan): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/or" testOr
  Tests.registerRoundtrip (.or)
