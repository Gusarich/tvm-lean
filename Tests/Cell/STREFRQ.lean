-- Auto-generated stub for TVM instruction STREFRQ (category: cell).
import Tests.Registry

open TvmLean Tests

def testStrefRq : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .endc
    , .newc
    , .xchg0 1
    , .cellOp (.strefR true)
    ]
  let (exitCode, st) ← expectHalt (← runProg prog)
  expectExitOk "strefRq" exitCode
  assert (st.stack.size == 2) s!"strefRq: unexpected stack size={st.stack.size}"
  match st.stack[0]!, st.stack.back! with
  | .builder b, .int (.num code) =>
      assert (code == 0) s!"strefRq: expected status 0, got {code}"
      assert (b.refs.size == 1) s!"strefRq: expected 1 ref, got {b.refs.size}"
  | v0, v1 =>
      throw (IO.userError s!"strefRq: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/strefRq" testStrefRq
  Tests.registerRoundtrip (.cellOp (.strefR true))
