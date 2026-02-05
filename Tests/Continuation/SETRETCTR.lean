import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETRETCTR

def testSETRETCTR : IO Unit := do
  let res ←
    Tests.runProgWith
      [ .contExt (.setRetCtr 1)
      , .pushCtr 0
      ]
      (fun st => { st with stack := #[.cont (.quit 123)] })
      80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SETRETCTR" code
  match st.stack.get? 0 with
  | some (.cont (.envelope _ cregs _)) =>
      assert (cregs.c1 == some (.quit 123)) s!"SETRETCTR: expected saved c1=quit123"
  | some v => throw (IO.userError s!"SETRETCTR: expected envelope cont, got {v.pretty}")
  | none => throw (IO.userError "SETRETCTR: empty stack")

initialize
  Tests.registerTest "continuation/SETRETCTR" testSETRETCTR
  Tests.registerRoundtrip (.contExt (.setRetCtr 0))

end Tests.Continuation.SETRETCTR
