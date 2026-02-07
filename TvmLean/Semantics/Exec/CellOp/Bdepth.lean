import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBdepth (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .bdepth =>
      let b ← VM.popBuilder
      let mut d : Nat := 0
      for r in b.refs do
        d := Nat.max d (r.depth + 1)
      VM.pushSmallInt (Int.ofNat d)
  | _ => next

end TvmLean
