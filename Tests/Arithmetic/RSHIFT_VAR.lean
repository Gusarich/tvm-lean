-- Auto-generated stub for TVM instruction RSHIFT_VAR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testRshiftVar : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 32), .pushInt (.num 5), .rshift ])
  expectExitOk "rshift_var(32,5)" exitCode1
  assert (st1.stack.size == 1) s!"rshift_var(32,5): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"rshift_var(32,5): expected 1, got {n}"
  | v => throw (IO.userError s!"rshift_var(32,5): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ←
    expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 5), .rshift ])
  expectExitOk "rshift_var(nan,5)" exitCodeNan
  assert (stNan.stack.size == 1) s!"rshift_var(nan,5): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"rshift_var(nan,5): expected NaN, got {v.pretty}")

  let (exitCodeBadShift, _) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 1024), .rshift ])
  expectExitExc "rshift_var(1,1024)" .rangeChk exitCodeBadShift

initialize
  Tests.registerTest "arith/rshift_var" testRshiftVar
  Tests.registerRoundtrip (.rshift)
