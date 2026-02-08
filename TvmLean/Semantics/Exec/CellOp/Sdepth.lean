import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSdepth (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .sdepth =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.cell.depth)
  | _ => next

end TvmLean
