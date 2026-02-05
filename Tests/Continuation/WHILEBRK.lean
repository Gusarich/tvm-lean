import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.WHILEBRK

def vInt (n : Int) : Value := .int (.num n)

def testWHILEBRK : IO Unit := do
  let condCell ←
    match assembleCp0 [ .pushInt (.num 1) ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let cond : Continuation := .ordinary (Slice.ofCell condCell) (.quit 0) OrdCregs.empty OrdCdata.empty
  let bodyCell ←
    match assembleCp0 [ .retAlt ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.while true)
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[.cont cond, .cont body] })
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"WHILEBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 777]) s!"WHILEBRK: expected [777], got {st.stack}"

initialize
  Tests.registerTest "continuation/WHILEBRK" testWHILEBRK
  Tests.registerRoundtrip (.contExt (.while true))

end Tests.Continuation.WHILEBRK
