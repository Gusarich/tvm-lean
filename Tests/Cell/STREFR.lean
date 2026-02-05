-- Auto-generated stub for TVM instruction STREFR (category: cell).
import Tests.Registry

open TvmLean Tests

def testStrefR : IO Unit := do
  let prog : List Instr :=
    [ .newc
    , .endc
    , .newc
    , .xchg0 1
    , .cellOp (.strefR false)
    , .cellOp .brefs
    ]
  let (exitCode, st) ← expectHalt (← runProg prog)
  expectExitOk "strefR" exitCode
  assert (st.stack.size == 1) s!"strefR: unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"strefR: expected 1, got {n}"
  | v => throw (IO.userError s!"strefR: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/strefR" testStrefR
  Tests.registerRoundtrip (.cellOp (.strefR false))
