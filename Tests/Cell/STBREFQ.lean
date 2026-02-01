-- Auto-generated stub for TVM instruction STBREFQ (category: cell).
import Tests.Registry

open TvmLean Tests

def testStbrefqSuccess : IO Unit := do
  let prog : List Instr := [ .newc, .newc, .xchg0 1, .stbRef false true ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stbrefq(success): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stbrefq(success): unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"stbrefq(success): unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .builder b, .int (.num status) =>
          assert (status == 0) s!"stbrefq(success): expected status 0, got {status}"
          assert (b.refs.size == 1) s!"stbrefq(success): expected 1 ref, got {b.refs.size}"
      | v0, v1 =>
          throw (IO.userError s!"stbrefq(success): unexpected stack values {v0.pretty}, {v1.pretty}")

def testStbrefqFail : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .newc, .endc, .xchg0 1, .stref
    , .newc, .endc, .xchg0 1, .stref
    , .newc, .endc, .xchg0 1, .stref
    , .newc, .endc, .xchg0 1, .stref
    , .newc, .xchg0 1, .stbRef false true
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stbrefq(fail): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stbrefq(fail): unexpected exitCode={exitCode}"
      assert (st.stack.size == 3) s!"stbrefq(fail): unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]!, st.stack[2]! with
      | .builder cb2, .builder b, .int (.num status) =>
          assert (status == -1) s!"stbrefq(fail): expected status -1, got {status}"
          assert (b.refs.size == 4) s!"stbrefq(fail): expected 4 refs, got {b.refs.size}"
          assert (cb2.refs.size == 0) s!"stbrefq(fail): expected empty cb2, got {cb2.refs.size}"
      | v0, v1, v2 =>
          throw (IO.userError s!"stbrefq(fail): unexpected stack values {v0.pretty}, {v1.pretty}, {v2.pretty}")

initialize
  Tests.registerTest "cell/stbrefq/success" testStbrefqSuccess
  Tests.registerTest "cell/stbrefq/fail" testStbrefqFail
  Tests.registerRoundtrip (.stbRef false true)
