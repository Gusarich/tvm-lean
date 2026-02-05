import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETALTCTR

def testSETALTCTR : IO Unit := do
  let res ←
    Tests.runProgWith
      [ .contExt (.setAltCtr 0)
      , .pushCtr 1
      ]
      (fun st => { st with stack := #[.cont (.quit 555)] })
      80
  let (code, st) ← Tests.expectHalt res
  -- RETALT may be used by the VM internally; accept either -1/-2.
  assert (code == -1 ∨ code == -2) s!"SETALTCTR: unexpected exitCode={code}"
  match st.stack.get? 0 with
  | some (.cont (.envelope _ cregs _)) =>
      assert (cregs.c0 == some (.quit 555)) s!"SETALTCTR: expected saved c0=quit555"
  | some v => throw (IO.userError s!"SETALTCTR: expected envelope cont, got {v.pretty}")
  | none => throw (IO.userError "SETALTCTR: empty stack")

initialize
  Tests.registerTest "continuation/SETALTCTR" testSETALTCTR
  Tests.registerRoundtrip (.contExt (.setAltCtr 7))

end Tests.Continuation.SETALTCTR
