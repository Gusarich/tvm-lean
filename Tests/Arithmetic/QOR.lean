-- Auto-generated stub for TVM instruction QOR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQor : IO Unit := do
  let (exitCode, st) ← expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 2), .contExt .qor ])
  expectExitOk "qor(5,2)" exitCode
  assert (st.stack.size == 1) s!"qor(5,2): unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) => assert (n == 7) s!"qor(5,2): expected 7, got {n}"
  | v => throw (IO.userError s!"qor(5,2): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qor" testQor
  Tests.registerRoundtrip (.contExt .qor)
