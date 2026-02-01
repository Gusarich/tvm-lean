-- Auto-generated stub for TVM instruction RSHIFT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testRshift : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 32), .pushInt (.num 5), .rshift ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "rshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"rshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"rshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"rshift: expected 1, got {n}"
      | v => throw (IO.userError s!"rshift: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/rshift" testRshift
  Tests.registerRoundtrip (.rshift)
