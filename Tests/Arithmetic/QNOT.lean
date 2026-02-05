-- Auto-generated stub for TVM instruction QNOT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQnot : IO Unit := do
  let (exitCode, st) ← expectHalt (← runProg [ .pushInt (.num 0), .contExt .qnot ])
  expectExitOk "qnot(0)" exitCode
  assert (st.stack.size == 1) s!"qnot(0): unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"qnot(0): expected -1, got {n}"
  | v => throw (IO.userError s!"qnot(0): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qnot" testQnot
  Tests.registerRoundtrip (.contExt .qnot)
