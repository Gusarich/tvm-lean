-- Auto-generated stub for TVM instruction DEBUGSTR (category: debug).
import Tests.Registry

open TvmLean Tests

def testDebugStr : IO Unit := do
  let bs : Array UInt8 := #[0x68, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64] -- "hello world"
  let s : Slice := Slice.ofCell (cellOfBytes bs)
  match (← runProg [(.debugOp (.debugStr s))]) with
  | .continue _ => throw (IO.userError "debugstr: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"debugstr: unexpected exitCode={exitCode}"
      assert (st.stack.isEmpty) s!"debugstr: unexpected stack size={st.stack.size}"

initialize
  Tests.registerTest "debug/debugstr" testDebugStr
  Tests.registerRoundtrip (.debugOp (.debugStr (Slice.ofCell (cellOfBytes #[0x00]))))
