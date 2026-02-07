import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdPpfxRev (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdPpfxRev =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let sBits := s.readBits s.bitsRemaining
      let ok : Bool := prefBits.size < sBits.size && sBits.extract 0 prefBits.size == prefBits
      VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
