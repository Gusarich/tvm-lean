import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdCntTrail0 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdCntTrail0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let endPos : Nat := s.cell.bits.size
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[endPos - 1 - cnt]! == false do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | _ => next

end TvmLean
