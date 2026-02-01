-- Auto-generated stub for TVM instruction MUL (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMul : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 6), .pushInt (.num 7), .mul ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "mul(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"mul(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"mul(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 42) s!"mul(pos): expected 42, got {n}"
      | v => throw (IO.userError s!"mul(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num 6), .pushInt (.num (-7)), .mul ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "mul(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"mul(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"mul(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -42) s!"mul(neg): expected -42, got {n}"
      | v => throw (IO.userError s!"mul(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/mul" testMul
  Tests.registerRoundtrip (.mul)
