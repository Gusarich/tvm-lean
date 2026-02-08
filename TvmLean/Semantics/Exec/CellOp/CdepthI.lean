import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpCdepthI (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .cdepthI i =>
      let c ← VM.popCell
      let info ←
        match c.computeLevelInfo? with
        | .ok v => pure v
        | .error _ => throw .cellUnd
      VM.pushSmallInt (Int.ofNat (info.getDepth i))
  | _ => next

end TvmLean
