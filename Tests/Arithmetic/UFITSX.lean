-- Auto-generated stub for TVM instruction UFITSX (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testUfitsx : IO Unit := do
  let (exitCodeOk, stOk) ← expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .contExt .ufitsx ])
  expectExitOk "ufitsx(7,3)" exitCodeOk
  assert (stOk.stack.size == 1) s!"ufitsx(7,3): unexpected stack size={stOk.stack.size}"
  match stOk.stack[0]! with
  | .int (.num n) => assert (n == 7) s!"ufitsx(7,3): expected 7, got {n}"
  | v => throw (IO.userError s!"ufitsx(7,3): unexpected stack value {v.pretty}")

  let (exitCodeNo, stNo) ← expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .contExt .ufitsx ])
  expectExitExc "ufitsx(8,3)" .intOv exitCodeNo
  assert (stNo.stack.size == 1) s!"ufitsx(8,3): unexpected stack size={stNo.stack.size}"
  match stNo.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"ufitsx(8,3): expected 0, got {n}"
  | v => throw (IO.userError s!"ufitsx(8,3): unexpected stack value {v.pretty}")

  let (exitCodeNeg, stNeg) ← expectHalt (← runProg [ .pushInt (.num (-1)), .pushInt (.num 3), .contExt .ufitsx ])
  expectExitExc "ufitsx(-1,3)" .intOv exitCodeNeg
  assert (stNeg.stack.size == 1) s!"ufitsx(-1,3): unexpected stack size={stNeg.stack.size}"
  match stNeg.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"ufitsx(-1,3): expected 0, got {n}"
  | v => throw (IO.userError s!"ufitsx(-1,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/ufitsx" testUfitsx
  Tests.registerRoundtrip (.contExt .ufitsx)
