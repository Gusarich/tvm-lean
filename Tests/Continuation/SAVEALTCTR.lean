import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SAVEALTCTR

def testSAVEALTCTR : IO Unit := do
  let res ← Tests.runProg [ .contExt (.saveAltCtr 2), .pushCtr 1 ] 80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SAVEALTCTR" code
  match st.stack.get? 0 with
  | some (.cont (.envelope _ cregs _)) =>
      assert (cregs.c2 == some .excQuit) s!"SAVEALTCTR: expected saved c2=excQuit"
  | some v => throw (IO.userError s!"SAVEALTCTR: expected envelope cont, got {v.pretty}")
  | none => throw (IO.userError "SAVEALTCTR: empty stack")

initialize
  Tests.registerTest "continuation/SAVEALTCTR" testSAVEALTCTR
  Tests.registerRoundtrip (.contExt (.saveAltCtr 7))

end Tests.Continuation.SAVEALTCTR
