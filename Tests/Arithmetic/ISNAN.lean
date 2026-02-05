-- Auto-generated stub for TVM instruction ISNAN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testIsnan : IO Unit := do
  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .contExt .isnan ])
  expectExitOk "isnan(NaN)" exitCodeNan
  assert (stNan.stack.size == 1) s!"isnan(NaN): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"isnan(NaN): expected -1, got {n}"
  | v => throw (IO.userError s!"isnan(NaN): unexpected stack value {v.pretty}")

  let (exitCodeNum, stNum) ← expectHalt (← runProg [ .pushInt (.num 7), .contExt .isnan ])
  expectExitOk "isnan(7)" exitCodeNum
  assert (stNum.stack.size == 1) s!"isnan(7): unexpected stack size={stNum.stack.size}"
  match stNum.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"isnan(7): expected 0, got {n}"
  | v => throw (IO.userError s!"isnan(7): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/isnan" testIsnan
  Tests.registerRoundtrip (.contExt .isnan)
