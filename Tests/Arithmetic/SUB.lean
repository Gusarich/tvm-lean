-- Auto-generated stub for TVM instruction SUB (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testSub : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 10), .pushInt (.num 4), .sub ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "sub: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sub: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sub: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 6) s!"sub: expected 6, got {n}"
      | v => throw (IO.userError s!"sub: unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-3)), .pushInt (.num 5), .sub ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "sub(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sub(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sub(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -8) s!"sub(neg): expected -8, got {n}"
      | v => throw (IO.userError s!"sub(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/sub" testSub
  Tests.registerRoundtrip (.sub)
