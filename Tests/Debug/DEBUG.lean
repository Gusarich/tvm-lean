-- Auto-generated stub for TVM instruction DEBUG (category: debug).
import Tests.Registry

open TvmLean Tests

def testDebug : IO Unit := do
  match (← runProg [(.debugOp (.debug 1))]) with
  | .continue _ => throw (IO.userError "debug: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"debug: unexpected exitCode={exitCode}"
      assert (st.stack.isEmpty) s!"debug: unexpected stack size={st.stack.size}"

initialize
  Tests.registerTest "debug/debug" testDebug
  Tests.registerRoundtrip (.debugOp (.debug 1))
