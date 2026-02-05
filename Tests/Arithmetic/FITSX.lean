-- Auto-generated stub for TVM instruction FITSX (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testFitsx : IO Unit := do
  let (exitCodeOk, stOk) ← expectHalt (← runProg [ .pushInt (.num 3), .pushInt (.num 3), .contExt .fitsx ])
  expectExitOk "fitsx(3,3)" exitCodeOk
  assert (stOk.stack.size == 1) s!"fitsx(3,3): unexpected stack size={stOk.stack.size}"
  match stOk.stack[0]! with
  | .int (.num n) => assert (n == 3) s!"fitsx(3,3): expected 3, got {n}"
  | v => throw (IO.userError s!"fitsx(3,3): unexpected stack value {v.pretty}")

  let (exitCodeNo, stNo) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .contExt .fitsx ])
  expectExitExc "fitsx(7,3)" .intOv exitCodeNo
  assert (stNo.stack.size == 1) s!"fitsx(7,3): unexpected stack size={stNo.stack.size}"
  match stNo.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"fitsx(7,3): expected 0, got {n}"
  | v => throw (IO.userError s!"fitsx(7,3): unexpected stack value {v.pretty}")

  let (exitCodeNeg, stNeg) ← expectHalt (← runProg [ .pushInt (.num (-4)), .pushInt (.num 3), .contExt .fitsx ])
  expectExitOk "fitsx(-4,3)" exitCodeNeg
  assert (stNeg.stack.size == 1) s!"fitsx(-4,3): unexpected stack size={stNeg.stack.size}"
  match stNeg.stack[0]! with
  | .int (.num n) => assert (n == -4) s!"fitsx(-4,3): expected -4, got {n}"
  | v => throw (IO.userError s!"fitsx(-4,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/fitsx" testFitsx
  Tests.registerRoundtrip (.contExt .fitsx)
