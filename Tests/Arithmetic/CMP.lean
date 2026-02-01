-- Auto-generated stub for TVM instruction CMP (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testCmp : IO Unit := do
  let progLt : List Instr := [ .pushInt (.num 3), .pushInt (.num 5), .cmp ]
  match (← runProg progLt) with
  | .continue _ => throw (IO.userError "cmp(lt): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"cmp(lt): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"cmp(lt): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"cmp(lt): expected -1, got {n}"
      | v => throw (IO.userError s!"cmp(lt): unexpected stack value {v.pretty}")

  let progEq : List Instr := [ .pushInt (.num 7), .pushInt (.num 7), .cmp ]
  match (← runProg progEq) with
  | .continue _ => throw (IO.userError "cmp(eq): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"cmp(eq): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"cmp(eq): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"cmp(eq): expected 0, got {n}"
      | v => throw (IO.userError s!"cmp(eq): unexpected stack value {v.pretty}")

  let progGt : List Instr := [ .pushInt (.num 9), .pushInt (.num 4), .cmp ]
  match (← runProg progGt) with
  | .continue _ => throw (IO.userError "cmp(gt): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"cmp(gt): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"cmp(gt): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 1) s!"cmp(gt): expected 1, got {n}"
      | v => throw (IO.userError s!"cmp(gt): unexpected stack value {v.pretty}")

  let codeCell ←
    match assembleCp0 [ .cmp ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"cmp(nan): assembleCp0 failed: {reprStr e}")
  let base := VmState.initial codeCell
  let st0Nan : VmState := { base with stack := #[.int .nan, .int (.num 1)] }
  match VmState.run 20 st0Nan with
  | .continue _ => throw (IO.userError "cmp(nan): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"cmp(nan): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"cmp(nan): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int .nan => pure ()
      | v => throw (IO.userError s!"cmp(nan): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/cmp" testCmp
  Tests.registerRoundtrip (.cmp)
