import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.UNTILBRK

def vInt (n : Int) : Value := .int (.num n)

def testUNTILBRK : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .retAlt ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let res ←
    Tests.runProgWith
      [ .contExt (.until true)
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[.cont body] })
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"UNTILBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 777]) s!"UNTILBRK: expected [777], got {st.stack}"

initialize
  Tests.registerTest "continuation/UNTILBRK" testUNTILBRK
  Tests.registerRoundtrip (.contExt (.until true))

end Tests.Continuation.UNTILBRK
