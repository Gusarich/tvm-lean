import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.UNTIL

def vInt (n : Int) : Value := .int (.num n)

def testUNTIL : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 1) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let res ←
    Tests.runProgWith
      [ .until
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[.cont body] })
      200
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "UNTIL" code
  assert (st.stack == #[vInt 777]) s!"UNTIL: expected [777], got {st.stack}"

initialize
  Tests.registerTest "continuation/UNTIL" testUNTIL
  Tests.registerRoundtrip (.until)

end Tests.Continuation.UNTIL
