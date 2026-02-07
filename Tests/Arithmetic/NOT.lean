-- Auto-generated stub for TVM instruction NOT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testNot : IO Unit := do
  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num 0), .not_ ])
  expectExitOk "not(0)" exitCode1
  assert (st1.stack.size == 1) s!"not(0): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"not(0): expected -1, got {n}"
  | v => throw (IO.userError s!"not(0): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .not_ ])
  -- NOT is non-quiet: NaN inputs raise integer overflow (see TON `exec_not` + `push_int_quiet`).
  expectExitExc "not(nan)" .intOv exitCodeNan
  assert (stNan.stack.size == 1) s!"not(nan): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"not(nan): expected 0, got {n}"
  | v => throw (IO.userError s!"not(nan): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/not" testNot
  Tests.registerRoundtrip (.not_)
