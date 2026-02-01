-- Auto-generated stub for TVM instruction BBITS (category: cell).
import Tests.Registry

open TvmLean Tests

def testBuilderBits : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .newc, .stu 1, .bbits ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "bbits: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"bbits: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"bbits: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"bbits: expected 1, got {n}"
      | v => throw (IO.userError s!"bbits: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/bbits" testBuilderBits
  Tests.registerRoundtrip (.bbits)
