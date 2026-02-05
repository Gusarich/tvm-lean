-- Auto-generated stub for TVM instruction SCUTFIRST (category: cell).
import Tests.Registry

open TvmLean Tests

def testScutfirst : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[true, false, true, true, false] #[Cell.empty, Cell.empty]
  let prog : List Instr := [ .pushInt (.num 2), .pushInt (.num 1), .cellOp .scutfirst, .sbitrefs ]
  let (exitCode, st) ←
    expectHalt <| (← runProgWith prog (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "scutfirst" exitCode
  assert (st.stack.size == 2) s!"scutfirst: unexpected stack size={st.stack.size}"
  match st.stack[0]!, st.stack.back! with
  | .int (.num bits), .int (.num refs) =>
      assert (bits == 2) s!"scutfirst: expected bits=2, got {bits}"
      assert (refs == 1) s!"scutfirst: expected refs=1, got {refs}"
  | v0, v1 =>
      throw (IO.userError s!"scutfirst: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/scutfirst" testScutfirst
  Tests.registerRoundtrip (.cellOp .scutfirst)
