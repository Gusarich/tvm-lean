import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackBlkSwap (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .blkSwap x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let front := st.stack.take (n - total)
        let below := st.stack.extract (n - total) (n - y)
        let top := st.stack.extract (n - y) n
        modify fun st => { st with stack := front ++ top ++ below }
      else
        throw .stkUnd
  | _ => next

end TvmLean
