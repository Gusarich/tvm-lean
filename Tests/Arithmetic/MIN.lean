-- Auto-generated stub for TVM instruction MIN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMin : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 5), .pushInt (.num 7), .min ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "min(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"min(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"min(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 5) s!"min(pos): expected 5, got {n}"
      | v => throw (IO.userError s!"min(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-3)), .pushInt (.num (-10)), .min ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "min(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"min(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"min(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -10) s!"min(neg): expected -10, got {n}"
      | v => throw (IO.userError s!"min(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/min" testMin
  Tests.registerRoundtrip (.min)
