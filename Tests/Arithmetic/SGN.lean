-- Auto-generated stub for TVM instruction SGN (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testSgn : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 12), .sgn ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "sgn(12): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sgn(12): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sgn(12): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"sgn(12): expected 1, got {n}"
      | v => throw (IO.userError s!"sgn(12): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-12)), .sgn ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "sgn(-12): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sgn(-12): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sgn(-12): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"sgn(-12): expected -1, got {n}"
      | v => throw (IO.userError s!"sgn(-12): unexpected stack value {v.pretty}")

  let progZero : List Instr := [ .pushInt (.num 0), .sgn ]
  match (← runProg progZero) with
  | .continue _ => throw (IO.userError "sgn(0): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sgn(0): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sgn(0): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"sgn(0): expected 0, got {n}"
      | v => throw (IO.userError s!"sgn(0): unexpected stack value {v.pretty}")

  let codeCell ←
    match assembleCp0 [ .sgn ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"sgn(nan): assembleCp0 failed: {reprStr e}")
  let base := VmState.initial codeCell
  let st0Nan : VmState := { base with stack := #[.int .nan] }
  match VmState.run 20 st0Nan with
  | .continue _ => throw (IO.userError "sgn(nan): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sgn(nan): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sgn(nan): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int .nan => pure ()
      | v => throw (IO.userError s!"sgn(nan): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/sgn" testSgn
  Tests.registerRoundtrip (.sgn)
