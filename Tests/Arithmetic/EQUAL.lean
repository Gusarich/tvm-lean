-- Auto-generated stub for TVM instruction EQUAL (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testEqual : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 10), .pushInt (.num 10), .equal ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "equal: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"equal: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"equal: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"equal: expected -1, got {n}"
      | v => throw (IO.userError s!"equal: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/equal" testEqual
  Tests.registerRoundtrip (.equal)
