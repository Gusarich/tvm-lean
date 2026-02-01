-- Auto-generated stub for TVM instruction LEQ (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testLeq : IO Unit := do
  let progLt : List Instr := [ .pushInt (.num 3), .pushInt (.num 5), .leq ]
  match (← runProg progLt) with
  | .continue _ => throw (IO.userError "leq(lt): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"leq(lt): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"leq(lt): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"leq(lt): expected -1, got {n}"
      | v => throw (IO.userError s!"leq(lt): unexpected stack value {v.pretty}")

  let progEq : List Instr := [ .pushInt (.num 5), .pushInt (.num 5), .leq ]
  match (← runProg progEq) with
  | .continue _ => throw (IO.userError "leq(eq): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"leq(eq): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"leq(eq): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"leq(eq): expected -1, got {n}"
      | v => throw (IO.userError s!"leq(eq): unexpected stack value {v.pretty}")

  let progGt : List Instr := [ .pushInt (.num 9), .pushInt (.num 4), .leq ]
  match (← runProg progGt) with
  | .continue _ => throw (IO.userError "leq(gt): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"leq(gt): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"leq(gt): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"leq(gt): expected 0, got {n}"
      | v => throw (IO.userError s!"leq(gt): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/leq" testLeq
  Tests.registerRoundtrip (.leq)
