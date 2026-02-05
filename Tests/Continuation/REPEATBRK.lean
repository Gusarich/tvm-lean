import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.REPEATBRK

def vInt (n : Int) : Value := .int (.num n)

def testREPEATBRK : IO Unit := do
  let bodyCell ←
    match assembleCp0 [ .retAlt ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let body : Continuation := .ordinary (Slice.ofCell bodyCell) (.quit 0) OrdCregs.empty OrdCdata.empty

  let res ←
    Tests.runProgWith
      [ .contExt (.repeat true)
      , .pushInt (.num 777)
      ]
      (fun st => { st with stack := #[vInt 0, vInt 10, .cont body] })
      200
  let (code, st) ← Tests.expectHalt res
  -- Accept normal or alt exit depending on c1/c0 details.
  assert (code == -1 ∨ code == -2) s!"REPEATBRK: unexpected exitCode={code}"
  assert (st.stack == #[vInt 0, vInt 777]) s!"REPEATBRK: expected [0,777], got {st.stack}"

initialize
  Tests.registerTest "continuation/REPEATBRK" testREPEATBRK
  Tests.registerRoundtrip (.contExt (.repeat true))

end Tests.Continuation.REPEATBRK
