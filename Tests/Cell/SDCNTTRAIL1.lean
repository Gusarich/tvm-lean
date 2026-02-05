-- Auto-generated stub for TVM instruction SDCNTTRAIL1 (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdCntTrail1 : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[false, true, false, true, true, true] #[]
  let (c, st) ←
    expectHalt <| (← runProgWith [ .cellOp .sdCntTrail1 ] (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "sdcnttrail1" c
  match st.stack[0]! with
  | .int (.num n) => assert (n == 3) s!"sdcnttrail1: expected 3, got {n}"
  | v => throw (IO.userError s!"sdcnttrail1: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdcnttrail1" testSdCntTrail1
  Tests.registerRoundtrip (.cellOp .sdCntTrail1)
