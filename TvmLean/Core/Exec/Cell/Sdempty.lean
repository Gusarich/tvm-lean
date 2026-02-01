import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdempty (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 then -1 else 0)
  | _ => next

end TvmLean
