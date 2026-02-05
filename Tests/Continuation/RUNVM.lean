import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.RUNVM

def vInt (n : Int) : Value := .int (.num n)

def testRUNVM : IO Unit := do
  let emptyCode ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let codeSlice : Slice := Slice.ofCell emptyCode

  -- mode=0: returns all stack values + result code 0.
  let res0 ←
    Tests.runProgWith
      [ .contExt (.runvm 0)
      , .pushInt (.num 999)
      ]
      (fun st =>
        { st with stack := #[vInt 11, vInt 22, vInt 2, .slice codeSlice] })
      1000
  let (code0, st0) ← Tests.expectHalt res0
  Tests.expectExitOk "RUNVM(mode0)" code0
  assert (st0.stack == #[vInt 11, vInt 22, vInt 0, vInt 999]) s!"RUNVM(mode0): got {st0.stack}"

  -- mode=256: return exactly N values.
  let res1 ←
    Tests.runProgWith
      [ .contExt (.runvm 256) ]
      (fun st =>
        { st with stack := #[vInt 11, vInt 22, vInt 2, .slice codeSlice, vInt 1] })
      1000
  let (code1, st1) ← Tests.expectHalt res1
  Tests.expectExitOk "RUNVM(retvals)" code1
  assert (st1.stack == #[vInt 22, vInt 0]) s!"RUNVM(retvals): got {st1.stack}"

initialize
  Tests.registerTest "continuation/RUNVM" testRUNVM
  Tests.registerRoundtrip (.contExt (.runvm 0))

end Tests.Continuation.RUNVM
