import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSrefs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .srefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | _ => next

end TvmLean
