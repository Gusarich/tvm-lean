-- Auto-generated stub for TVM instruction QFITSX (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQfitsx : IO Unit := do
  let (exitCodeNo, stNo) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .contExt .qfitsx ])
  expectExitOk "qfitsx(7,3)" exitCodeNo
  assert (stNo.stack.size == 1) s!"qfitsx(7,3): unexpected stack size={stNo.stack.size}"
  match stNo.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qfitsx(7,3): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qfitsx" testQfitsx
  Tests.registerRoundtrip (.contExt .qfitsx)
