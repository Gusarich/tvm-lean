-- Auto-generated stub for TVM instruction SDSFXREV (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdSfxRev : IO Unit := do
  let a : Cell := Cell.mkOrdinary #[true, false, true, false, true, false] #[]
  let b : Cell := Cell.mkOrdinary #[true, false] #[]

  let (c, st) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdSfxRev ] (fun st => { st with stack := #[.slice (Slice.ofCell a), .slice (Slice.ofCell b)] }))
  expectExitOk "sdsfxrev" c
  match st.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"sdsfxrev: expected -1, got {n}"
  | v => throw (IO.userError s!"sdsfxrev: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdsfxrev" testSdSfxRev
  Tests.registerRoundtrip (.cellOp .sdSfxRev)
