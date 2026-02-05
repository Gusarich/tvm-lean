-- Auto-generated stub for TVM instruction SSKIPFIRST (category: cell).
import Tests.Registry

open TvmLean Tests

def testSskipfirst : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[true, false, true, true, false] #[Cell.empty, Cell.empty]
  let prog : List Instr := [ .pushInt (.num 2), .pushInt (.num 1), .cellOp .sskipfirst, .sbitrefs ]
  let (exitCode, st) ←
    expectHalt <| (← runProgWith prog (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "sskipfirst" exitCode
  assert (st.stack.size == 2) s!"sskipfirst: unexpected stack size={st.stack.size}"
  match st.stack[0]!, st.stack.back! with
  | .int (.num bits), .int (.num refs) =>
      assert (bits == 3) s!"sskipfirst: expected bits=3, got {bits}"
      assert (refs == 1) s!"sskipfirst: expected refs=1, got {refs}"
  | v0, v1 =>
      throw (IO.userError s!"sskipfirst: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/sskipfirst" testSskipfirst
  Tests.registerRoundtrip (.cellOp .sskipfirst)
