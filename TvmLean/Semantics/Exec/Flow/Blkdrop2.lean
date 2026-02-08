import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowBlkdrop2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .blkdrop2 x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let keepBottom : Nat := st.stack.size - total
        let bottom := st.stack.take keepBottom
        let top := st.stack.extract (keepBottom + x) st.stack.size
        modify fun st => { st with stack := bottom ++ top }
      else
        throw .stkUnd
  | _ => next

end TvmLean
