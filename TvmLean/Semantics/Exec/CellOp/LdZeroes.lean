import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpLdZeroes (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .ldZeroes =>
      let s ← VM.popSlice
      let n := s.countLeading false
      let s' := if n > 0 then s.advanceBits n else s
      VM.pushSmallInt (Int.ofNat n)
      VM.push (.slice s')
  | _ => next

end TvmLean
