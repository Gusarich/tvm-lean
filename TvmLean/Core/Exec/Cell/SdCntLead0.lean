import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdCntLead0 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdCntLead0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[s.bitPos + cnt]! == false do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | _ => next

end TvmLean
