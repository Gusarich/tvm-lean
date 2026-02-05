-- Auto-generated stub for TVM instruction DEBUG_1 (category: debug).
import Tests.Registry

open TvmLean Tests

def testDebug1 : IO Unit := do
  match (← runProg [(.debugOp (.debug1 0x15))]) with
  | .continue _ => throw (IO.userError "debug_1: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"debug_1: unexpected exitCode={exitCode}"
      assert (st.stack.isEmpty) s!"debug_1: unexpected stack size={st.stack.size}"

initialize
  Tests.registerTest "debug/debug_1" testDebug1
  Tests.registerRoundtrip (.debugOp (.debug1 0x15))
