import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdPfx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdPfx =>
      -- Match C++ `exec_bin_cs_cmp`: pop cs2 (top), then cs1, and compute cs1.is_prefix_of(cs2).
      let s ← VM.popSlice
      let pref ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
