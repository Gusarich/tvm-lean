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
  -- RSHIFT is non-quiet: NaN inputs raise integer overflow (see TON `exec_rshift` + `push_int_quiet`).
  expectExitExc "rshift(nan,5)" .intOv exitCodeXNan
  assert (stXNan.stack.size == 1) s!"rshift(nan,5): unexpected stack size={stXNan.stack.size}"
  match stXNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"rshift(nan,5): expected 0, got {n}"
  | v => throw (IO.userError s!"rshift(nan,5): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/rshift" testRshift
  Tests.registerRoundtrip (.rshiftConst false 5)
