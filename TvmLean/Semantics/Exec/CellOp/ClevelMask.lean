import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpClevelMask (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .clevelMask =>
      let c ← VM.popCell
      VM.pushSmallInt (Int.ofNat c.levelMask)
  | _ => next

end TvmLean
