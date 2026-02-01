-- Auto-generated stub for TVM instruction STBREF (category: cell).
import Tests.Registry

open TvmLean Tests

def testStbRef : IO Unit := do
  let prog : List Instr :=
    [ .pushInt (.num 1)
    , .newc
    , .stu 1
    , .newc
    , .stbRef false false
    , .cellOp .brefs
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stbref: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stbref: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"stbref: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"stbref: expected 1 ref, got {n}"
      | v => throw (IO.userError s!"stbref: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/stbref" testStbRef
  Tests.registerRoundtrip (.stbRef false false)
