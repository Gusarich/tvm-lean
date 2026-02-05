-- Auto-generated stub for TVM instruction QRSHIFT_VAR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQrshiftVar : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 32), .pushInt (.num 5), .arithExt (.rshiftVar true) ])
  expectExitOk "qrshift_var(32,5)" exitCode1
  assert (st1.stack.size == 1) s!"qrshift_var(32,5): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"qrshift_var(32,5): expected 1, got {n}"
  | v => throw (IO.userError s!"qrshift_var(32,5): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qrshift_var" testQrshiftVar
  Tests.registerRoundtrip (.arithExt (.rshiftVar true))
