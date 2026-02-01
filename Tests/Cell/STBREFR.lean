-- Auto-generated stub for TVM instruction STBREFR (category: cell).
import Tests.Registry

open TvmLean Tests

def testStbRefR : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .newc
    , .stbRef true false
    , .cellOp .brefs
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stbrefr: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stbrefr: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"stbrefr: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"stbrefr: expected 1, got {n}"
      | v => throw (IO.userError s!"stbrefr: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/stbrefr" testStbRefR
  Tests.registerRoundtrip (.stbRef true false)
