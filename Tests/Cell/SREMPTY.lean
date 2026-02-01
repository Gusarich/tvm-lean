-- Auto-generated stub for TVM instruction SREMPTY (category: cell).
import Tests.Registry

open TvmLean Tests

def runSrempty (s : Slice) : Except Excno VmState :=
  let codeCell : Cell := Cell.mkOrdinary #[] #[]
  let base := VmState.initial codeCell
  let st0 : VmState := { base with stack := #[.slice s] }
  let (res, st1) := (execInstr .srempty).run st0
  match res with
  | .ok _ => .ok st1
  | .error e => .error e

def testSrempty : IO Unit := do
  let emptySlice := Slice.ofCell (Cell.mkOrdinary #[] #[])
  let refCell : Cell := Cell.mkOrdinary #[] #[]
  let sliceWithRef := Slice.ofCell (Cell.mkOrdinary #[] #[refCell])

  match runSrempty emptySlice with
  | .error e => throw (IO.userError s!"srempty(empty): error {reprStr e}")
  | .ok st =>
      assert (st.stack.size == 1) s!"srempty(empty): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -1) s!"srempty(empty): expected -1, got {n}"
      | v => throw (IO.userError s!"srempty(empty): unexpected stack value {v.pretty}")

  match runSrempty sliceWithRef with
  | .error e => throw (IO.userError s!"srempty(ref): error {reprStr e}")
  | .ok st =>
      assert (st.stack.size == 1) s!"srempty(ref): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 0) s!"srempty(ref): expected 0, got {n}"
      | v => throw (IO.userError s!"srempty(ref): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/srempty" testSrempty
