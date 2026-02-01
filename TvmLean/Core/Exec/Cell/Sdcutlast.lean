import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdcutlast (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdcutlast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let drop : Nat := s.bitsRemaining - bits
        VM.push (.slice (s.advanceBits drop))
      else
        throw .cellUnd
  | _ => next

end TvmLean
