-- Auto-generated stub for TVM instruction QMIN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQmin : IO Unit := do
  let (exitCodeOk, stOk) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .contExt .qmin ])
  expectExitOk "qmin(7,3)" exitCodeOk
  assert (stOk.stack.size == 1) s!"qmin(7,3): unexpected stack size={stOk.stack.size}"
  match stOk.stack[0]! with
  | .int (.num n) => assert (n == 3) s!"qmin(7,3): expected 3, got {n}"
  | v => throw (IO.userError s!"qmin(7,3): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 3), .contExt .qmin ])
  expectExitOk "qmin(NaN,3)" exitCodeNan
  assert (stNan.stack.size == 1) s!"qmin(NaN,3): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qmin(NaN,3): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qmin" testQmin
  Tests.registerRoundtrip (.contExt .qmin)
