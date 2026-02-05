import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.UNTILENDBRK

def vInt (n : Int) : Value := .int (.num n)

def testUNTILENDBRK : IO Unit := do
  let res ←
    Tests.runProg
      [ .pushInt (.num 999)
      , .contExt (.untilEnd true)
      , .retAlt
      , .pushInt (.num 777)
      ]
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"UNTILENDBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 999]) s!"UNTILENDBRK: expected [999], got {st.stack}"

initialize
  Tests.registerTest "continuation/UNTILENDBRK" testUNTILENDBRK
  Tests.registerRoundtrip (.contExt (.untilEnd true))

end Tests.Continuation.UNTILENDBRK
