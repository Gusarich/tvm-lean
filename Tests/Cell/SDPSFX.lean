-- Auto-generated stub for TVM instruction SDPSFX (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdPsfx : IO Unit := do
  let whole : Cell := Cell.mkOrdinary #[true, false, true, false] #[]
  let suf : Cell := Cell.mkOrdinary #[true, false] #[]
  let eq : Cell := Cell.mkOrdinary #[true, false, true, false] #[]

  let (cOk, stOk) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdPsfx ] (fun st => { st with stack := #[.slice (Slice.ofCell suf), .slice (Slice.ofCell whole)] }))
  expectExitOk "sdpsfx(ok)" cOk
  match stOk.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"sdpsfx(ok): expected -1, got {n}"
  | v => throw (IO.userError s!"sdpsfx(ok): unexpected stack value {v.pretty}")

  let (cEq, stEq) ←
    expectHalt <|
      (← runProgWith [ .cellOp .sdPsfx ] (fun st => { st with stack := #[.slice (Slice.ofCell eq), .slice (Slice.ofCell eq)] }))
  expectExitOk "sdpsfx(eq)" cEq
  match stEq.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"sdpsfx(eq): expected 0, got {n}"
  | v => throw (IO.userError s!"sdpsfx(eq): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdpsfx" testSdPsfx
  Tests.registerRoundtrip (.cellOp .sdPsfx)
