-- Auto-generated stub for TVM instruction BREMBITREFS (category: cell).
import Tests.Registry

open TvmLean Tests

def testBuilderRemBitRefs : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .newc, .stu 1, .cellOp .brembitrefs ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "brembitrefs: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"brembitrefs: unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"brembitrefs: unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .int (.num bits), .int (.num refs) =>
          assert (bits == 1022 ∧ refs == 4) s!"brembitrefs: expected [1022,4], got {Stack.pretty st.stack}"
      | _, _ =>
          throw (IO.userError s!"brembitrefs: unexpected stack value {Stack.pretty st.stack}")

initialize
  Tests.registerTest "cell/brembitrefs" testBuilderRemBitRefs
  Tests.registerRoundtrip (.cellOp .brembitrefs)
