-- Auto-generated stub for TVM instruction MAX (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMax : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 3), .pushInt (.num 7), .max ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "max(positive): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"max(positive): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"max(positive): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 7) s!"max(positive): expected 7, got {n}"
      | v => throw (IO.userError s!"max(positive): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-5)), .pushInt (.num (-10)), .max ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "max(negative): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"max(negative): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"max(negative): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -5) s!"max(negative): expected -5, got {n}"
      | v => throw (IO.userError s!"max(negative): unexpected stack value {v.pretty}")

  let progNan : List Instr := [ .pushInt .nan, .pushInt (.num 5), .max ]
  match (← runProg progNan) with
  | .continue _ => throw (IO.userError "max(nan): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"max(nan): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"max(nan): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int .nan => pure ()
      | v => throw (IO.userError s!"max(nan): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/max" testMax
  Tests.registerRoundtrip (.max)
