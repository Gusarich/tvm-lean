import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpCdepthIX (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .cdepthIX =>
      let i ← VM.popNatUpTo 3
      let c ← VM.popCell
      let info ←
        match c.computeLevelInfo? with
        | .ok v => pure v
        | .error _ => throw .cellUnd
      VM.pushSmallInt (Int.ofNat (info.getDepth i))
  | _ => next

end TvmLean
