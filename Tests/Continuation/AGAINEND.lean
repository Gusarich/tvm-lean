import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.AGAINEND

def vInt (n : Int) : Value := .int (.num n)

def testAGAINEND : IO Unit := do
  let res ←
    Tests.runProg
      [ .contExt (.againEnd false)
      , .pushInt (.num 42)
      , .retAlt
      ]
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -2) s!"AGAINEND: expected alt halt (-2), got {code}"
  assert (st.stack == #[vInt 42]) s!"AGAINEND: expected [42], got {st.stack}"

initialize
  Tests.registerTest "continuation/AGAINEND" testAGAINEND
  Tests.registerRoundtrip (.contExt (.againEnd false))

end Tests.Continuation.AGAINEND
