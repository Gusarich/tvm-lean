import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.AGAINENDBRK

def vInt (n : Int) : Value := .int (.num n)

def testAGAINENDBRK : IO Unit := do
  let res ←
    Tests.runProg
      [ .contExt (.againEnd true)
      , .pushInt (.num 42)
      , .retAlt
      ]
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"AGAINENDBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 42]) s!"AGAINENDBRK: expected [42], got {st.stack}"

initialize
  Tests.registerTest "continuation/AGAINENDBRK" testAGAINENDBRK
  Tests.registerRoundtrip (.contExt (.againEnd true))

end Tests.Continuation.AGAINENDBRK
