import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.POPSAVE

def testPOPSAVE : IO Unit := do
  let res ←
    Tests.runProgWith
      [ .contExt (.popSave 2)
      , .pushCtr 2
      , .pushCtr 0
      ]
      (fun st => { st with stack := #[.cont (.quit 77)] })
      100
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "POPSAVE" code
  assert (st.stack.size == 2) s!"POPSAVE: expected 2 items, got {st.stack.size}"
  match st.stack[0]!, st.stack[1]! with
  | .cont (.quit 77), .cont (.envelope _ cregs _) =>
      assert (cregs.c2 == some .excQuit) s!"POPSAVE: expected saved c2=excQuit"
  | v0, v1 => throw (IO.userError s!"POPSAVE: unexpected stack [{v0.pretty}, {v1.pretty}]")

initialize
  Tests.registerTest "continuation/POPSAVE" testPOPSAVE
  Tests.registerRoundtrip (.contExt (.popSave 0))

end Tests.Continuation.POPSAVE
