-- Auto-generated stub for TVM instruction BITSIZE (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testBitsize : IO Unit := do
  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .bitsize ])
  expectExitOk "bitsize(0)" exitCode0
  assert (st0.stack.size == 1) s!"bitsize(0): unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"bitsize(0): expected 0, got {n}"
  | v => throw (IO.userError s!"bitsize(0): unexpected stack value {v.pretty}")

  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num 1), .bitsize ])
  expectExitOk "bitsize(1)" exitCode1
  assert (st1.stack.size == 1) s!"bitsize(1): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"bitsize(1): expected 2, got {n}"
  | v => throw (IO.userError s!"bitsize(1): unexpected stack value {v.pretty}")

  let (exitCodeNeg1, stNeg1) ← expectHalt (← runProg [ .pushInt (.num (-1)), .bitsize ])
  expectExitOk "bitsize(-1)" exitCodeNeg1
  assert (stNeg1.stack.size == 1) s!"bitsize(-1): unexpected stack size={stNeg1.stack.size}"
  match stNeg1.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"bitsize(-1): expected 1, got {n}"
  | v => throw (IO.userError s!"bitsize(-1): unexpected stack value {v.pretty}")

  let (exitCodeNan, _) ← expectHalt (← runProg [ .pushInt .nan, .bitsize ])
  expectExitExc "bitsize(nan)" .intOv exitCodeNan

initialize
  Tests.registerTest "arith/bitsize" testBitsize
  Tests.registerRoundtrip (.bitsize)
