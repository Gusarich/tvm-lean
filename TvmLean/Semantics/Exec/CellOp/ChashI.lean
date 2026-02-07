import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpChashI (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .chashI i =>
      let c ← VM.popCell
      let info ←
        match c.computeLevelInfo? with
        | .ok v => pure v
        | .error _ => throw .cellUnd
      let h := info.getHash i
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | _ => next

end TvmLean
