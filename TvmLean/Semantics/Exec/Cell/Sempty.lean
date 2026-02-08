import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSempty (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 && s.refsRemaining == 0 then -1 else 0)
  | _ => next

end TvmLean
