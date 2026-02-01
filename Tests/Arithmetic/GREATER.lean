-- Auto-generated stub for TVM instruction GREATER (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testGreater : IO Unit := do
  let runCase (x y expected : Int) : IO Unit := do
    let prog : List Instr := [ .pushInt (.num x), .pushInt (.num y), .greater ]
    match (← runProg prog) with
    | .continue _ => throw (IO.userError "greater: did not halt")
    | .halt exitCode st =>
        assert (exitCode == -1) s!"greater: unexpected exitCode={exitCode}"
        assert (st.stack.size == 1) s!"greater: unexpected stack size={st.stack.size}"
        match st.stack[0]! with
        | .int (.num n) => assert (n == expected) s!"greater: expected {expected}, got {n}"
        | v => throw (IO.userError s!"greater: unexpected stack value {v.pretty}")
  runCase 10 5 (-1)
  runCase 5 10 0

initialize
  Tests.registerTest "arith/greater" testGreater
  Tests.registerRoundtrip (.greater)
