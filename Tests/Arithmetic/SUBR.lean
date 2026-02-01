-- Auto-generated stub for TVM instruction SUBR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testSubr : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 5), .pushInt (.num 2), .subr ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "subr: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"subr: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"subr: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -3) s!"subr: expected -3, got {n}"
      | v => throw (IO.userError s!"subr: unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-7)), .pushInt (.num 4), .subr ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "subr(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"subr(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"subr(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 11) s!"subr(neg): expected 11, got {n}"
      | v => throw (IO.userError s!"subr(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/subr" testSubr
  Tests.registerRoundtrip (.subr)
