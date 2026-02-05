-- Auto-generated stub for TVM instruction DUMPSTK (category: debug).
import Tests.Registry

open TvmLean Tests

def testDumpStk : IO Unit := do
  match (← runProg [(.debugOp .dumpStk)]) with
  | .continue _ => throw (IO.userError "dumpstk: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"dumpstk: unexpected exitCode={exitCode}"
      assert (st.stack.isEmpty) s!"dumpstk: unexpected stack size={st.stack.size}"

initialize
  Tests.registerTest "debug/dumpstk" testDumpStk
  Tests.registerRoundtrip (.debugOp .dumpStk)
