import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowBlkdrop (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .blkdrop n =>
      let st ← get
      if n ≤ st.stack.size then
        let keep : Nat := st.stack.size - n
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | _ => next

end TvmLean
