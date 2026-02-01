-- Auto-generated stub for TVM instruction BREMBITS (category: cell).
import Tests.Registry

open TvmLean Tests

def testBuilderRemainingBits : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .newc, .stu 1, .cellOp .brembits ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "brembits: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"brembits: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"brembits: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1022) s!"brembits: expected 1022, got {n}"
      | v => throw (IO.userError s!"brembits: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/brembits" testBuilderRemainingBits
  Tests.registerRoundtrip (.cellOp .brembits)
