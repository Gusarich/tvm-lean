-- Auto-generated stub for TVM instruction DEBUG_2 (category: debug).
import Tests.Registry

open TvmLean Tests

def testDebug2 : IO Unit := do
  match (← runProg [(.debugOp (.debug2 0x30))]) with
  | .continue _ => throw (IO.userError "debug_2: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"debug_2: unexpected exitCode={exitCode}"
      assert (st.stack.isEmpty) s!"debug_2: unexpected stack size={st.stack.size}"

initialize
  Tests.registerTest "debug/debug_2" testDebug2
  Tests.registerRoundtrip (.debugOp (.debug2 0x30))
