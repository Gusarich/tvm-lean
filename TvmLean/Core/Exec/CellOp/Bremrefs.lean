import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBremrefs (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .bremrefs =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat (4 - b.refs.size))
  | _ => next

end TvmLean
