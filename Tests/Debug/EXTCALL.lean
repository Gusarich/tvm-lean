-- Auto-generated stub for TVM instruction EXTCALL (category: debug).
import Tests.Registry

open TvmLean Tests

def testExtCall : IO Unit := do
  let (exitCode, st) ← expectHalt (← runProg [(.debugOp (.extCall 0))])
  expectExitExc "extcall" .invOpcode exitCode
  assert (st.stack.size == 1) s!"extcall: unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) =>
      assert (n == 0) s!"extcall: expected 0 remaining on stack, got {n}"
  | v =>
      throw (IO.userError s!"extcall: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "debug/extcall" testExtCall
  Tests.registerRoundtrip (.debugOp (.extCall 0))
