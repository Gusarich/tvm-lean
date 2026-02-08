import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpLdOnes (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .ldOnes =>
      let s ← VM.popSlice
      let n := s.countLeading true
      let s' := if n > 0 then s.advanceBits n else s
      VM.pushSmallInt (Int.ofNat n)
      VM.push (.slice s')
  | _ => next

end TvmLean
