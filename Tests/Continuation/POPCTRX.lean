import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.POPCTRX

def vInt (n : Int) : Value := .int (.num n)

def testPOPCTRX : IO Unit := do
  let res ←
    Tests.runProgWith
      [ .contExt .popCtrX
      , .pushCtr 2
      ]
      (fun st =>
        { st with
          stack := #[.cont (.quit 99), vInt 2] })
      80
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "POPCTRX" code
  assert (st.stack.size == 1) s!"POPCTRX: expected 1 item, got {st.stack.size}"
  match st.stack[0]! with
  | .cont (.quit 99) => pure ()
  | v => throw (IO.userError s!"POPCTRX: expected cont quit99, got {v.pretty}")

  let resBad ←
    Tests.runProgWith [ .contExt .popCtrX ] (fun st => { st with stack := #[vInt 123, vInt 0] }) 40
  let (codeBad, _) ← Tests.expectHalt resBad
  Tests.expectExitExc "POPCTRX(typeChk)" .typeChk codeBad

initialize
  Tests.registerTest "continuation/POPCTRX" testPOPCTRX
  Tests.registerRoundtrip (.contExt .popCtrX)

end Tests.Continuation.POPCTRX
