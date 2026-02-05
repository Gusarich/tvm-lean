-- Auto-generated stub for TVM instruction RSHIFT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testRshift : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 32), .rshiftConst false 5 ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "rshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"rshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"rshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"rshift: expected 1, got {n}"
      | v => throw (IO.userError s!"rshift: unexpected stack value {v.pretty}")

  let (exitCodeXNan, stXNan) ← expectHalt (← runProg [ .pushInt .nan, .rshiftConst false 5 ])
  expectExitOk "rshift(nan,5)" exitCodeXNan
  assert (stXNan.stack.size == 1) s!"rshift(nan,5): unexpected stack size={stXNan.stack.size}"
  match stXNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"rshift(nan,5): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/rshift" testRshift
  Tests.registerRoundtrip (.rshiftConst false 5)
