-- Auto-generated stub for TVM instruction QXOR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQxor : IO Unit := do
  let (exitCode, st) ← expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 3), .contExt .qxor ])
  expectExitOk "qxor(5,3)" exitCode
  assert (st.stack.size == 1) s!"qxor(5,3): unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) => assert (n == 6) s!"qxor(5,3): expected 6, got {n}"
  | v => throw (IO.userError s!"qxor(5,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qxor" testQxor
  Tests.registerRoundtrip (.contExt .qxor)
