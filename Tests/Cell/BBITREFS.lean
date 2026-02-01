-- Auto-generated stub for TVM instruction BBITREFS (category: cell).
import Tests.Registry

open TvmLean Tests

def testBuilderBitRefs : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .endc
    , .pushInt (.num 5)
    , .newc
    , .stu 3
    , .stref
    , .cellOp .bbitrefs
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "bbitrefs: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"bbitrefs: unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"bbitrefs: unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .int (.num bits), .int (.num refs) =>
          assert (bits == 3 ∧ refs == 1) s!"bbitrefs: expected [bits=3,refs=1], got {Stack.pretty st.stack}"
      | _, _ =>
          throw (IO.userError s!"bbitrefs: unexpected stack {Stack.pretty st.stack}")

initialize
  Tests.registerTest "cell/bbitrefs" testBuilderBitRefs
  Tests.registerRoundtrip (.cellOp .bbitrefs)
