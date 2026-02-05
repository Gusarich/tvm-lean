-- Auto-generated stub for TVM instruction SDSUBSTR (category: cell).
import Tests.Registry

open TvmLean Tests

def testSdSubstr : IO Unit := do
  let cell : Cell := Cell.mkOrdinary #[true, false, true, true, false, false] #[]
  let prog : List Instr := [ .pushInt (.num 2), .pushInt (.num 3), .cellOp .sdSubstr, .ldu 3 ]
  let (exitCode, st) ←
    expectHalt <| (← runProgWith prog (fun st => { st with stack := #[.slice (Slice.ofCell cell)] }))
  expectExitOk "sdsubstr" exitCode
  assert (st.stack.size == 2) s!"sdsubstr: unexpected stack size={st.stack.size}"
  match st.stack[0]! with
  | .int (.num n) => assert (n == 6) s!"sdsubstr: expected 6 (bits 110), got {n}"
  | v => throw (IO.userError s!"sdsubstr: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sdsubstr" testSdSubstr
  Tests.registerRoundtrip (.cellOp .sdSubstr)
