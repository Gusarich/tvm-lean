-- Auto-generated stub for TVM instruction LSHIFT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testLshift : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .pushInt (.num 5), .lshift ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "lshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"lshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"lshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 32) s!"lshift: expected 32, got {n}"
      | v => throw (IO.userError s!"lshift: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/lshift" testLshift
  Tests.registerRoundtrip (.lshift)
