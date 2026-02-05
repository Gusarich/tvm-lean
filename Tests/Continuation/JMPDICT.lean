import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.JMPDICT

def vInt (n : Int) : Value := .int (.num n)

def testJMPDICT : IO Unit := do
  let calleeCell ←
    match assembleCp0 [ .pushInt (.num 123) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let callee : Continuation := .ordinary (Slice.ofCell calleeCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.jmpDict 5)
      , .pushInt (.num 777)
      ]
      (fun st =>
        { st with regs := { st.regs with c3 := callee } })
      200
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "JMPDICT" code
  assert (st.stack == #[vInt 5, vInt 123]) s!"JMPDICT: expected [5,123], got {st.stack}"

initialize
  Tests.registerTest "continuation/JMPDICT" testJMPDICT
  Tests.registerRoundtrip (.contExt (.jmpDict 0))

end Tests.Continuation.JMPDICT
