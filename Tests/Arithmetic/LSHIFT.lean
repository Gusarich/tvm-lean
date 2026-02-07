-- Auto-generated stub for TVM instruction LSHIFT (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testLshift : IO Unit := do
  let prog : List Instr := [ .pushInt (.num 1), .lshiftConst false 5 ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "lshift: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"lshift: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"lshift: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 32) s!"lshift: expected 32, got {n}"
      | v => throw (IO.userError s!"lshift: unexpected stack value {v.pretty}")

  let (exitCodeXNan, stXNan) ← expectHalt (← runProg [ .pushInt .nan, .lshiftConst false 5 ])
  -- LSHIFT is non-quiet: NaN inputs raise integer overflow (see TON `exec_lshift` + `push_int_quiet`).
  expectExitExc "lshift(nan,5)" .intOv exitCodeXNan
  assert (stXNan.stack.size == 1) s!"lshift(nan,5): unexpected stack size={stXNan.stack.size}"
  match stXNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"lshift(nan,5): expected 0, got {n}"
  | v => throw (IO.userError s!"lshift(nan,5): expected 0, got {v.pretty}")

  let (exitCodeOv, _) ← expectHalt (← runProg [ .pushInt (.num 1), .lshiftConst false 256 ])
  expectExitExc "lshift(1,256)" .intOv exitCodeOv

initialize
  Tests.registerTest "arith/lshift" testLshift
  Tests.registerRoundtrip (.lshiftConst false 5)
