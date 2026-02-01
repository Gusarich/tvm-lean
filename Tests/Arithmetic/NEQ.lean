-- Auto-generated stub for TVM instruction NEQ (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testNeq : IO Unit := do
  let progNotEqual : List Instr := [ .pushInt (.num 10), .pushInt (.num 11), .neq ]
  match (← runProg progNotEqual) with
  | .continue _ => throw (IO.userError "neq(10,11): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"neq(10,11): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"neq(10,11): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"neq(10,11): expected -1, got {n}"
      | v => throw (IO.userError s!"neq(10,11): unexpected stack value {v.pretty}")

  let progEqual : List Instr := [ .pushInt (.num 7), .pushInt (.num 7), .neq ]
  match (← runProg progEqual) with
  | .continue _ => throw (IO.userError "neq(7,7): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"neq(7,7): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"neq(7,7): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"neq(7,7): expected 0, got {n}"
      | v => throw (IO.userError s!"neq(7,7): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/neq" testNeq
  Tests.registerRoundtrip (.neq)
