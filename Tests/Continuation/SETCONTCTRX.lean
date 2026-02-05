import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.SETCONTCTRX

def vInt (n : Int) : Value := .int (.num n)

def testSETCONTCTRX : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .pushInt (.num 7) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let res ←
    Tests.runProgWith
      [ .contExt .setContCtrX ]
      (fun st =>
        -- Stack: x c i
        { st with stack := #[.cont (.quit 123), .cont body, vInt 1] })
      80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "SETCONTCTRX" code
  assert (st.stack.size == 1) s!"SETCONTCTRX: expected 1 item, got {st.stack.size}"
  match st.stack[0]! with
  | .cont (.ordinary _ _ cregs _) =>
      assert (cregs.c1 == some (.quit 123)) s!"SETCONTCTRX: expected saved c1=quit123"
  | v => throw (IO.userError s!"SETCONTCTRX: expected cont, got {v.pretty}")

initialize
  Tests.registerTest "continuation/SETCONTCTRX" testSETCONTCTRX
  Tests.registerRoundtrip (.contExt .setContCtrX)

end Tests.Continuation.SETCONTCTRX
