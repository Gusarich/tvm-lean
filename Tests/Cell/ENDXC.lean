-- Auto-generated stub for TVM instruction ENDXC (category: cell).
import Tests.Registry

open TvmLean Tests

def testEndxc : IO Unit := do
  -- ENDXC finalizes a builder with a `special` boolean flag (exotic cell).
  -- An empty builder cannot be finalized into a valid exotic cell, so use `special=false` here.
  let prog : List Instr := [ .newc, .pushInt (.num 0), .cellOp .endxc, .xctos ]
  let (exitCode, st) ← expectHalt (← runProg prog)
  expectExitOk "endxc" exitCode
  assert (st.stack.size == 2) s!"endxc: unexpected stack size={st.stack.size}"
  match st.stack.back! with
  | .int (.num n) => assert (n == 0) s!"endxc: expected special=0, got {n}"
  | v => throw (IO.userError s!"endxc: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/endxc" testEndxc
  Tests.registerRoundtrip (.cellOp .endxc)
