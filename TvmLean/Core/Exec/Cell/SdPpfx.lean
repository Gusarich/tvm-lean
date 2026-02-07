import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdPpfx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdPpfx =>
      -- Match C++ `exec_bin_cs_cmp`: pop cs2 (top), then cs1, and compute cs1.is_proper_prefix_of(cs2).
      let s ← VM.popSlice
      let pref ← VM.popSlice
      -- Matches C++ `CellSlice::is_proper_prefix_of`: compare only remaining bits (ignore refs).
      let prefBits := pref.readBits pref.bitsRemaining
      let sBits := s.readBits s.bitsRemaining
      let ok : Bool := prefBits.size < sBits.size && sBits.take prefBits.size == prefBits
      VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
