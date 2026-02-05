-- Auto-generated stub for TVM instruction QBITSIZE (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQbitsize : IO Unit := do
  let (exitCode0, st0) ← expectHalt (← runProg [ .pushInt (.num 0), .contExt .qbitsize ])
  expectExitOk "qbitsize(0)" exitCode0
  assert (st0.stack.size == 1) s!"qbitsize(0): unexpected stack size={st0.stack.size}"
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qbitsize(0): expected 0, got {n}"
  | v => throw (IO.userError s!"qbitsize(0): unexpected stack value {v.pretty}")

  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num 1), .contExt .qbitsize ])
  expectExitOk "qbitsize(1)" exitCode1
  assert (st1.stack.size == 1) s!"qbitsize(1): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"qbitsize(1): expected 2, got {n}"
  | v => throw (IO.userError s!"qbitsize(1): unexpected stack value {v.pretty}")

  let (exitCodeNeg, stNeg) ← expectHalt (← runProg [ .pushInt (.num (-1)), .contExt .qbitsize ])
  expectExitOk "qbitsize(-1)" exitCodeNeg
  assert (stNeg.stack.size == 1) s!"qbitsize(-1): unexpected stack size={stNeg.stack.size}"
  match stNeg.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"qbitsize(-1): expected 1, got {n}"
  | v => throw (IO.userError s!"qbitsize(-1): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .contExt .qbitsize ])
  expectExitOk "qbitsize(NaN)" exitCodeNan
  assert (stNan.stack.size == 1) s!"qbitsize(NaN): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"qbitsize(NaN): expected 0, got {n}"
  | v => throw (IO.userError s!"qbitsize(NaN): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qbitsize" testQbitsize
  Tests.registerRoundtrip (.contExt .qbitsize)
