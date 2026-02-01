import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdBeginsX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdBeginsX quiet =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        VM.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | _ => next

end TvmLean
