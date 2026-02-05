import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.WHILEEND

def vInt (n : Int) : Value := .int (.num n)

def testWHILEEND : IO Unit := do
  let condCell ←
    match assembleCp0 [ .push 0 ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let cond : Continuation := .ordinary (Slice.ofCell condCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.whileEnd false)
      , .dec
      ]
      (fun st => { st with stack := #[vInt 3, .cont cond] })
      800
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "WHILEEND" code
  assert (st.stack == #[vInt 0]) s!"WHILEEND: expected [0], got {st.stack}"

initialize
  Tests.registerTest "continuation/WHILEEND" testWHILEEND
  Tests.registerRoundtrip (.contExt (.whileEnd false))

end Tests.Continuation.WHILEEND
