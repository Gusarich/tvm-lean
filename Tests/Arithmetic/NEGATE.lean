-- Auto-generated stub for TVM instruction NEGATE (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testNegate : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 7), .negate ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "negate(7): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"negate(7): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"negate(7): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -7) s!"negate(7): expected -7, got {n}"
      | v => throw (IO.userError s!"negate(7): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-13)), .negate ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "negate(-13): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"negate(-13): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"negate(-13): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 13) s!"negate(-13): expected 13, got {n}"
      | v => throw (IO.userError s!"negate(-13): unexpected stack value {v.pretty}")

  let progZero : List Instr := [ .pushInt (.num 0), .negate ]
  match (← runProg progZero) with
  | .continue _ => throw (IO.userError "negate(0): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"negate(0): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"negate(0): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"negate(0): expected 0, got {n}"
      | v => throw (IO.userError s!"negate(0): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/negate" testNegate
  Tests.registerRoundtrip (.negate)
