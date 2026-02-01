-- Auto-generated stub for TVM instruction QSUB (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQsub : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 12), .pushInt (.num 7), .qsub ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "qsub: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"qsub: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"qsub: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 5) s!"qsub: expected 5, got {n}"
      | v => throw (IO.userError s!"qsub: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/qsub" testQsub
  Tests.registerRoundtrip (.qsub)
