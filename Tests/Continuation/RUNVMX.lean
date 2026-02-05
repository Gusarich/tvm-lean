import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.RUNVMX

def vInt (n : Int) : Value := .int (.num n)

def testRUNVMX : IO Unit := do
  let emptyCode ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let codeSlice : Slice := Slice.ofCell emptyCode

  let res ←
    Tests.runProgWith
      [ .contExt .runvmx ]
      (fun st =>
        -- stack: entries (11,22), size=2, code, mode=0
        { st with stack := #[vInt 11, vInt 22, vInt 2, .slice codeSlice, vInt 0] })
      1000
  let (code, st) ← Tests.expectHalt res
  Tests.expectExitOk "RUNVMX" code
  assert (st.stack == #[vInt 11, vInt 22, vInt 0]) s!"RUNVMX: got {st.stack}"

initialize
  Tests.registerTest "continuation/RUNVMX" testRUNVMX
  Tests.registerRoundtrip (.contExt .runvmx)

end Tests.Continuation.RUNVMX
