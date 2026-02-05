import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.CALLDICT_LONG

def vInt (n : Int) : Value := .int (.num n)

def testCALLDICT_LONG : IO Unit := do
  let calleeCell ←
    match assembleCp0 [ .pushInt (.num 123) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let callee : Continuation := .ordinary (Slice.ofCell calleeCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .callDict 300
      , .pushInt (.num 777)
      ]
      (fun st =>
        { st with regs := { st.regs with c3 := callee } })
      300
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "CALLDICT_LONG" code
  assert (st.stack == #[vInt 300, vInt 123, vInt 777]) s!"CALLDICT_LONG: expected [300,123,777], got {st.stack}"

initialize
  Tests.registerTest "continuation/CALLDICT_LONG" testCALLDICT_LONG
  Tests.registerRoundtrip (.callDict 300)

end Tests.Continuation.CALLDICT_LONG
