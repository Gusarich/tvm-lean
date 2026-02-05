-- Auto-generated stub for TVM instruction QUFITSX (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQufitsx : IO Unit := do
  let (exitCodeNo, stNo) ← expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .contExt .qufitsx ])
  expectExitOk "qufitsx(8,3)" exitCodeNo
  assert (stNo.stack.size == 1) s!"qufitsx(8,3): unexpected stack size={stNo.stack.size}"
  match stNo.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qufitsx(8,3): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qufitsx" testQufitsx
  Tests.registerRoundtrip (.contExt .qufitsx)
