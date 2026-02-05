import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.UNTILEND

def vInt (n : Int) : Value := .int (.num n)

def testUNTILEND : IO Unit := do
  let res ←
    Tests.runProg
      [ .pushInt (.num 3)
      , .contExt (.untilEnd false)
      , .dec
      , .push 0
      , .pushInt (.num 0)
      , .equal
      ]
      600
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "UNTILEND" code
  assert (st.stack == #[vInt 0]) s!"UNTILEND: expected [0], got {st.stack}"

initialize
  Tests.registerTest "continuation/UNTILEND" testUNTILEND
  Tests.registerRoundtrip (.contExt (.untilEnd false))

end Tests.Continuation.UNTILEND
