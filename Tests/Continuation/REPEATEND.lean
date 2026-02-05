import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.REPEATEND

def vInt (n : Int) : Value := .int (.num n)

def testREPEATEND : IO Unit := do
  let res ←
    Tests.runProg
      [ .pushInt (.num 0)
      , .pushInt (.num 3)
      , .contExt (.repeatEnd false)
      , .pushInt (.num 1)
      , .add
      ]
      400
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "REPEATEND" code
  assert (st.stack == #[vInt 3]) s!"REPEATEND: expected [3], got {st.stack}"

initialize
  Tests.registerTest "continuation/REPEATEND" testREPEATEND
  Tests.registerRoundtrip (.contExt (.repeatEnd false))

end Tests.Continuation.REPEATEND
