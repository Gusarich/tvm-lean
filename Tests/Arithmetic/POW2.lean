-- Auto-generated stub for TVM instruction POW2 (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testPow2 : IO Unit := do
  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .contExt .pow2 ])
  expectExitOk "pow2(0)" exitCode0
  assert (st0.stack.size == 1) s!"pow2(0): unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"pow2(0): expected 1, got {n}"
  | v => throw (IO.userError s!"pow2(0): unexpected stack value {v.pretty}")

  let (exitCode3, st3) ← expectHalt (← runProg [ .pushInt (.num 3), .contExt .pow2 ])
  expectExitOk "pow2(3)" exitCode3
  assert (st3.stack.size == 1) s!"pow2(3): unexpected stack size={st3.stack.size}"
  match st3.stack[0]! with
  | .int (.num n) => assert (n == 8) s!"pow2(3): expected 8, got {n}"
  | v => throw (IO.userError s!"pow2(3): unexpected stack value {v.pretty}")

  let (exitCodeOv, _) ← expectHalt (← runProg [ .pushInt (.num 300), .contExt .pow2 ])
  expectExitExc "pow2(300)" .intOv exitCodeOv

initialize
  Tests.registerTest "arith/pow2" testPow2
  Tests.registerRoundtrip (.contExt .pow2)
