import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpClevel (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .clevel =>
      let c ← VM.popCell
      VM.pushSmallInt (Int.ofNat (LevelMask.getLevel c.levelMask))
  | _ => next

end TvmLean
