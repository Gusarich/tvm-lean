-- Auto-generated stub for TVM instruction XOR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testXor : IO Unit := do
  let (exitCode1, st1) ← expectHalt (← runProg [ .pushInt (.num (-1)), .pushInt (.num 1), .xor ])
  expectExitOk "xor(-1,1)" exitCode1
  assert (st1.stack.size == 1) s!"xor(-1,1): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"xor(-1,1): expected -2, got {n}"
  | v => throw (IO.userError s!"xor(-1,1): unexpected stack value {v.pretty}")

  let (exitCodeNan, stNan) ← expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 1), .xor ])
  -- XOR is non-quiet: NaN inputs raise integer overflow (see TON `exec_xor` + `push_int_quiet`).
  expectExitExc "xor(nan,1)" .intOv exitCodeNan
  assert (stNan.stack.size == 1) s!"xor(nan,1): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"xor(nan,1): expected 0, got {n}"
  | v => throw (IO.userError s!"xor(nan,1): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/xor" testXor
  Tests.registerRoundtrip (.xor)
