import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETCONTCTRMANY

def testSETCONTCTRMANY : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 7) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ← Tests.runProgWith [ .contExt (.setContCtrMany 3) ] (fun st => { st with stack := #[.cont body] }) 80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SETCONTCTRMANY" code
  match st.stack.get? 0 with
  | some (.cont (.ordinary _ _ cregs _)) =>
      assert (cregs.c0 == some (.quit 0)) s!"SETCONTCTRMANY: expected saved c0=quit0"
      assert (cregs.c1 == some (.quit 1)) s!"SETCONTCTRMANY: expected saved c1=quit1"
  | some v => throw (IO.userError s!"SETCONTCTRMANY: expected cont, got {v.pretty}")
  | none => throw (IO.userError "SETCONTCTRMANY: empty stack")

  let resBad ← Tests.runProgWith [ .contExt (.setContCtrMany 64) ] (fun st => { st with stack := #[.cont body] }) 60
  let (codeBad, _) ← Tests.expectHalt resBad
  Tests.expectExitExc "SETCONTCTRMANY(mask bit6)" .rangeChk codeBad

initialize
  Tests.registerTest "continuation/SETCONTCTRMANY" testSETCONTCTRMANY
  Tests.registerRoundtrip (.contExt (.setContCtrMany 0))

end Tests.Continuation.SETCONTCTRMANY
