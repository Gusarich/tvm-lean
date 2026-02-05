-- Auto-generated stub for TVM instruction SDSFX (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdSfx : IO Unit := do
  let whole : Cell := Cell.mkOrdinary #[true, false, true, false, true, false] #[]
  let sufOK : Cell := Cell.mkOrdinary #[true, false] #[]
  let sufNo : Cell := Cell.mkOrdinary #[false, false] #[]

  let (cOk, stOk) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdSfx ] (fun st => { st with stack := #[.slice (Slice.ofCell sufOK), .slice (Slice.ofCell whole)] }))
  expectExitOk "sdsfx(ok)" cOk
  match stOk.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"sdsfx(ok): expected -1, got {n}"
  | v => throw (IO.userError s!"sdsfx(ok): unexpected stack value {v.pretty}")

  let (cNo, stNo) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdSfx ] (fun st => { st with stack := #[.slice (Slice.ofCell sufNo), .slice (Slice.ofCell whole)] }))
  expectExitOk "sdsfx(no)" cNo
  match stNo.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"sdsfx(no): expected 0, got {n}"
  | v => throw (IO.userError s!"sdsfx(no): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdsfx" testSdSfx
  Tests.registerRoundtrip (.cellOp .sdSfx)
