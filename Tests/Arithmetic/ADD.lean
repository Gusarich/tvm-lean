-- Auto-generated stub for TVM instruction ADD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAdd : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 7), .pushInt (.num 5), .add ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "add(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"add(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"add(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 12) s!"add(pos): expected 12, got {n}"
      | v => throw (IO.userError s!"add(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-3)), .pushInt (.num 10), .add ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "add(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"add(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"add(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 7) s!"add(neg): expected 7, got {n}"
      | v => throw (IO.userError s!"add(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/add" testAdd
  Tests.registerRoundtrip (.add)
