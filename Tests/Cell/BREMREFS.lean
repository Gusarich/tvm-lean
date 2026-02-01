-- Auto-generated stub for TVM instruction BREMREFS (category: cell).
import Tests.Registry

open TvmLean Tests

def testBuilderRemRefs : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .newc
    , .endc
    , .xchg0 1
    , .stref
    , .cellOp .bremrefs
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "bremrefs: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"bremrefs: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"bremrefs: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 3) s!"bremrefs: expected 3, got {n}"
      | v => throw (IO.userError s!"bremrefs: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/bremrefs" testBuilderRemRefs
  Tests.registerRoundtrip (.cellOp .bremrefs)
