-- Auto-generated stub for TVM instruction SCUTLAST (category: cell).
import Tests.Registry

open TvmLean Tests

def testScutlast : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[true, false, true, true, false] #[Cell.empty, Cell.empty]
  let prog : List Instr := [ .pushInt (.num 2), .pushInt (.num 1), .cellOp .scutlast, .sbitrefs ]
  let (exitCode, st) ←
    expectHalt <| (← runProgWith prog (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "scutlast" exitCode
  assert (st.stack.size == 2) s!"scutlast: unexpected stack size={st.stack.size}"
  match st.stack[0]!, st.stack.back! with
  | .int (.num bits), .int (.num refs) =>
      assert (bits == 2) s!"scutlast: expected bits=2, got {bits}"
      assert (refs == 1) s!"scutlast: expected refs=1, got {refs}"
  | v0, v1 =>
      throw (IO.userError s!"scutlast: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/scutlast" testScutlast
  Tests.registerRoundtrip (.cellOp .scutlast)
