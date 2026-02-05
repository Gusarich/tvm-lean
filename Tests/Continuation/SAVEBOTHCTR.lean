import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SAVEBOTHCTR

def testSAVEBOTHCTR : IO Unit := do
  let res ← Tests.runProg [ .contExt (.saveBothCtr 2), .pushCtr 0, .pushCtr 1 ] 120
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SAVEBOTHCTR" code
  assert (st.stack.size == 2) s!"SAVEBOTHCTR: expected 2 items, got {st.stack.size}"
  match st.stack[0]!, st.stack[1]! with
  | .cont (.envelope _ cregs0 _), .cont (.envelope _ cregs1 _) =>
      assert (cregs0.c2 == some .excQuit) s!"SAVEBOTHCTR: expected saved c0.c2=excQuit"
      assert (cregs1.c2 == some .excQuit) s!"SAVEBOTHCTR: expected saved c1.c2=excQuit"
  | v0, v1 => throw (IO.userError s!"SAVEBOTHCTR: unexpected stack [{v0.pretty}, {v1.pretty}]")

initialize
  Tests.registerTest "continuation/SAVEBOTHCTR" testSAVEBOTHCTR
  Tests.registerRoundtrip (.contExt (.saveBothCtr 2))

end Tests.Continuation.SAVEBOTHCTR
