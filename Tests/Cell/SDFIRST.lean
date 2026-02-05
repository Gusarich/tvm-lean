-- Auto-generated stub for TVM instruction SDFIRST (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdFirst : IO Unit := do
  let cell1 : Cell := Cell.mkOrdinary #[true, false, false] #[]
  let cell0 : Cell := Cell.mkOrdinary #[false, true, false] #[]
  let empty : Cell := Cell.mkOrdinary #[] #[]

  let (c1, st1) ←
    expectHalt <| (← runProgWith [ .cellOp .sdFirst ] (fun st => { st with stack := #[.slice (Slice.ofCell cell1)] }))
  expectExitOk "sdfirst(1...)" c1
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"sdfirst(1...): expected -1, got {n}"
  | v => throw (IO.userError s!"sdfirst(1...): unexpected stack value {v.pretty}")

  let (c0, st0) ←
    expectHalt <| (← runProgWith [ .cellOp .sdFirst ] (fun st => { st with stack := #[.slice (Slice.ofCell cell0)] }))
  expectExitOk "sdfirst(0...)" c0
  match st0.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"sdfirst(0...): expected 0, got {n}"
  | v => throw (IO.userError s!"sdfirst(0...): unexpected stack value {v.pretty}")

  let (ce, ste) ←
    expectHalt <| (← runProgWith [ .cellOp .sdFirst ] (fun st => { st with stack := #[.slice (Slice.ofCell empty)] }))
  expectExitOk "sdfirst(empty)" ce
  match ste.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"sdfirst(empty): expected 0, got {n}"
  | v => throw (IO.userError s!"sdfirst(empty): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdfirst" testSdFirst
  Tests.registerRoundtrip (.cellOp .sdFirst)
