-- Auto-generated stub for TVM instruction SDCNTLEAD1 (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdCntLead1 : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[true, true, true, false, true] #[]
  let (c, st) ←
    expectHalt <| (← runProgWith [ .cellOp .sdCntLead1 ] (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "sdcntlead1" c
  match st.stack[0]! with
  | .int (.num n) => assert (n == 3) s!"sdcntlead1: expected 3, got {n}"
  | v => throw (IO.userError s!"sdcntlead1: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdcntlead1" testSdCntLead1
  Tests.registerRoundtrip (.cellOp .sdCntLead1)
