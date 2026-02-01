import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackNop (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nop =>
      pure ()
  | _ => next

end TvmLean
