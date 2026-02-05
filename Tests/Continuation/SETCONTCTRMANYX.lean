import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETCONTCTRMANYX

def vInt (n : Int) : Value := .int (.num n)

def testSETCONTCTRMANYX : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 7) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt .setContCtrManyX ]
      (fun st => { st with stack := #[.cont body, vInt 3] })
      80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SETCONTCTRMANYX" code
  match st.stack.get? 0 with
  | some (.cont (.ordinary _ _ cregs _)) =>
      assert (cregs.c0 == some (.quit 0)) s!"SETCONTCTRMANYX: expected saved c0=quit0"
      assert (cregs.c1 == some (.quit 1)) s!"SETCONTCTRMANYX: expected saved c1=quit1"
  | some v => throw (IO.userError s!"SETCONTCTRMANYX: expected cont, got {v.pretty}")
  | none => throw (IO.userError "SETCONTCTRMANYX: empty stack")

initialize
  Tests.registerTest "continuation/SETCONTCTRMANYX" testSETCONTCTRMANYX
  Tests.registerRoundtrip (.contExt .setContCtrManyX)

end Tests.Continuation.SETCONTCTRMANYX
