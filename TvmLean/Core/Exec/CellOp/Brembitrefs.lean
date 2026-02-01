import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBrembitrefs (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .brembitrefs =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat (1023 - b.bits.size))
      VM.pushSmallInt (Int.ofNat (4 - b.refs.size))
  | _ => next

end TvmLean
