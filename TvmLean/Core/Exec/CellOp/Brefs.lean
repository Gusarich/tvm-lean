import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBrefs (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .brefs =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat b.refs.size)
  | _ => next

end TvmLean
