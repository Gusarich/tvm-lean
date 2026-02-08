import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowDrop2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .drop2 =>
      let st ← get
      if 2 ≤ st.stack.size then
        let keep : Nat := st.stack.size - 2
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | _ => next

end TvmLean
