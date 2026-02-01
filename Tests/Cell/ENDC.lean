-- Auto-generated stub for TVM instruction ENDC (category: cell).
import Tests.Registry

open TvmLean Tests

def testEndc : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 3), .newc, .stu 2, .endc, .ctos, .ldu 2, .ends ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "endc: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"endc: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"endc: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 3) s!"endc: expected 3, got {n}"
      | v => throw (IO.userError s!"endc: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/endc" testEndc
  Tests.registerRoundtrip (.endc)
