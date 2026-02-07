import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpLdSame (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .ldSame =>
      VM.checkUnderflow 2
      let bNat ← VM.popNatUpTo 1
      let s ← VM.popSlice
      let b : Bool := bNat = 1
      let n := s.countLeading b
      let s' := if n > 0 then s.advanceBits n else s
      VM.pushSmallInt (Int.ofNat n)
      VM.push (.slice s')
  | _ => next

end TvmLean
