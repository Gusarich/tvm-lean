import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETEXITALT

def testSETEXITALT : IO Unit := do
  let emptyCell ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let k : Continuation := .ordinary (Slice.ofCell emptyCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let res ←
    Tests.runProgWith
      [ .contExt .setExitAlt
      , .pushCtr 1
      ]
      (fun st => { st with stack := #[.cont k] })
      80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SETEXITALT" code
  match st.stack.get? 0 with
  | some (.cont (.ordinary _ _ cregs _)) =>
      assert (cregs.c0 == some (.quit 0)) s!"SETEXITALT: expected saved c0=quit0"
      assert (cregs.c1 == some (.quit 1)) s!"SETEXITALT: expected saved c1=quit1"
  | some v => throw (IO.userError s!"SETEXITALT: expected cont, got {v.pretty}")
  | none => throw (IO.userError "SETEXITALT: empty stack")

initialize
  Tests.registerTest "continuation/SETEXITALT" testSETEXITALT
  Tests.registerRoundtrip (.contExt .setExitAlt)

end Tests.Continuation.SETEXITALT
