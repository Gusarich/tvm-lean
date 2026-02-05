import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.WHILE

def vInt (n : Int) : Value := .int (.num n)

def testWHILE : IO Unit := do
  let condCell ←
    match assembleCp0 [ .pushInt (.num 0) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let cond : Continuation := .ordinary (Slice.ofCell condCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 123) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let res ←
    Tests.runProgWith
      [ .while_
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[.cont cond, .cont body] })
      200
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "WHILE" code
  assert (st.stack == #[vInt 777]) s!"WHILE: expected [777], got {st.stack}"

initialize
  Tests.registerTest "continuation/WHILE" testWHILE
  Tests.registerRoundtrip (.while_)

end Tests.Continuation.WHILE
