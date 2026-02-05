-- Auto-generated stub for TVM instruction CHKNAN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testChknan : IO Unit := do
  let (exitCodeNum, stNum) ← expectHalt (← runProg [ .pushInt (.num 7), .contExt .chknan ])
  expectExitOk "chknan(7)" exitCodeNum
  assert (stNum.stack.size == 1) s!"chknan(7): unexpected stack size={stNum.stack.size}"
  match stNum.stack[0]! with
  | .int (.num n) => assert (n == 7) s!"chknan(7): expected 7, got {n}"
  | v => throw (IO.userError s!"chknan(7): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .contExt .chknan ])
  expectExitOk "chknan(NaN)" exitCodeNan
  assert (stNan.stack.size == 1) s!"chknan(NaN): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"chknan(NaN): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/chknan" testChknan
  Tests.registerRoundtrip (.contExt .chknan)
