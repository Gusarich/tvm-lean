import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBbitrefs (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .bbitrefs =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat b.bits.size)
      VM.pushSmallInt (Int.ofNat b.refs.size)
  | _ => next

end TvmLean
