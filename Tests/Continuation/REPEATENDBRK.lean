import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.REPEATENDBRK

def vInt (n : Int) : Value := .int (.num n)

def testREPEATENDBRK : IO Unit := do
  let res ←
    Tests.runProg
      [ .pushInt (.num 0)
      , .pushInt (.num 10)
      , .contExt (.repeatEnd true)
      , .retAlt
      ]
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"REPEATENDBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 0]) s!"REPEATENDBRK: expected [0], got {st.stack}"

initialize
  Tests.registerTest "continuation/REPEATENDBRK" testREPEATENDBRK
  Tests.registerRoundtrip (.contExt (.repeatEnd true))

end Tests.Continuation.REPEATENDBRK
