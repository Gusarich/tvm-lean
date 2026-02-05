import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.REPEAT

def vInt (n : Int) : Value := .int (.num n)

def testREPEAT : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 1), .add ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.repeat false)
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[vInt 0, vInt 3, .cont body] })
      400
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "REPEAT" code
  assert (st.stack == #[vInt 3, vInt 777]) s!"REPEAT: expected [3,777], got {st.stack}"

initialize
  Tests.registerTest "continuation/REPEAT" testREPEAT
  Tests.registerRoundtrip (.contExt (.repeat false))

end Tests.Continuation.REPEAT
