-- Auto-generated stub for TVM instruction INC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testInc : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 41), .inc ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "inc(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"inc(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"inc(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 42) s!"inc(pos): expected 42, got {n}"
      | v => throw (IO.userError s!"inc(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-2)), .inc ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "inc(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"inc(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"inc(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"inc(neg): expected -1, got {n}"
      | v => throw (IO.userError s!"inc(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/inc" testInc
  Tests.registerRoundtrip (.inc)
