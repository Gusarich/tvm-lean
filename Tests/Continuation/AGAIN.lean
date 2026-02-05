import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.AGAIN

def vInt (n : Int) : Value := .int (.num n)

def testAGAIN : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 42), .retAlt ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ← Tests.runProgWith [ .contExt (.again false) ] (fun st => { st with stack := #[.cont body] }) 200
  let (code, st) ← Tests.expectHalt res
  assert (code == -2) s!"AGAIN: expected alt halt (-2), got {code}"
  assert (st.stack == #[vInt 42]) s!"AGAIN: expected [42], got {st.stack}"

initialize
  Tests.registerTest "continuation/AGAIN" testAGAIN
  Tests.registerRoundtrip (.contExt (.again false))

end Tests.Continuation.AGAIN
