import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.PUSHCTRX

def vInt (n : Int) : Value := .int (.num n)

def testPUSHCTRX : IO Unit := do
  let res ← Tests.runProgWith [ .contExt .pushCtrX ] (fun st => { st with stack := #[vInt 0] }) 50
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "PUSHCTRX" code
  assert (st.stack.size == 1) s!"PUSHCTRX: expected 1 item, got {st.stack.size}"
  match st.stack[0]! with
  | .cont (.quit 0) => pure ()
  | v => throw (IO.userError s!"PUSHCTRX: expected cont quit0, got {v.pretty}")

initialize
  Tests.registerTest "continuation/PUSHCTRX" testPUSHCTRX
  Tests.registerRoundtrip (.contExt .pushCtrX)

end Tests.Continuation.PUSHCTRX
