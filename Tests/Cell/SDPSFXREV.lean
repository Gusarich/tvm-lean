-- Auto-generated stub for TVM instruction SDPSFXREV (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdPsfxRev : IO Unit := do
  let whole : Cell := Cell.mkOrdinary #[true, false, true, false] #[]
  let suf : Cell := Cell.mkOrdinary #[true, false] #[]

  let (c, st) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdPsfxRev ] (fun st => { st with stack := #[.slice (Slice.ofCell whole), .slice (Slice.ofCell suf)] }))
  expectExitOk "sdpsfxrev" c
  match st.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"sdpsfxrev: expected -1, got {n}"
  | v => throw (IO.userError s!"sdpsfxrev: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdpsfxrev" testSdPsfxRev
  Tests.registerRoundtrip (.cellOp .sdPsfxRev)
