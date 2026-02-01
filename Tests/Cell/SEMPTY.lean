-- Auto-generated stub for TVM instruction SEMPTY (category: cell).
import Tests.Registry

open TvmLean Tests

def testSempty : IO Unit := do
  let codeCell ←
    match assembleCp0 [ .sempty ] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")

  let base := VmState.initial codeCell

  let emptySlice := Slice.ofCell Cell.empty
  let stEmpty : VmState := { base with stack := #[.slice emptySlice] }
  match VmState.run 20 stEmpty with
  | .continue _ => throw (IO.userError "sempty(empty): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sempty(empty): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sempty(empty): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"sempty(empty): expected -1, got {n}"
      | v => throw (IO.userError s!"sempty(empty): unexpected stack value {v.pretty}")

  let nonEmptyCell := Cell.mkOrdinary (natToBits 1 1) #[Cell.empty]
  let nonEmptySlice := Slice.ofCell nonEmptyCell
  let stNonEmpty : VmState := { base with stack := #[.slice nonEmptySlice] }
  match VmState.run 20 stNonEmpty with
  | .continue _ => throw (IO.userError "sempty(non-empty): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"sempty(non-empty): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"sempty(non-empty): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"sempty(non-empty): expected 0, got {n}"
      | v => throw (IO.userError s!"sempty(non-empty): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/sempty" testSempty
  Tests.registerRoundtrip (.sempty)
