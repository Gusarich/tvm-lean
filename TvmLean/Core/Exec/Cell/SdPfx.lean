import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdPfx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdPfx =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
