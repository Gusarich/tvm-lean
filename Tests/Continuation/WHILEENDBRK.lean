import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.WHILEENDBRK

def vInt (n : Int) : Value := .int (.num n)

def testWHILEENDBRK : IO Unit := do
  let condCell ←
    match assembleCp0 [ .push 0 ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let cond : Continuation := .ordinary (Slice.ofCell condCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.whileEnd true)
      , .retAlt
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[vInt 999, .cont cond] })
      200
  let (code, st) ← Tests.expectHalt res
  assert (code == -1 ∨ code == -2) s!"WHILEENDBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 999]) s!"WHILEENDBRK: expected [999], got {st.stack}"

initialize
  Tests.registerTest "continuation/WHILEENDBRK" testWHILEENDBRK
  Tests.registerRoundtrip (.contExt (.whileEnd true))

end Tests.Continuation.WHILEENDBRK
