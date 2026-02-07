import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdskipfirst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdskipfirst =>
      VM.checkUnderflow 2
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | _ => next

end TvmLean
