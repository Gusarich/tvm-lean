import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdPfxRev (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdPfxRev =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
