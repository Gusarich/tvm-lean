import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBrembits (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .brembits =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat (1023 - b.bits.size))
  | _ => next

end TvmLean
