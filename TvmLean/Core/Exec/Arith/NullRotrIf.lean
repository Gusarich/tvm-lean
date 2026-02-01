import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullRotrIf (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullRotrIf =>
      VM.execNullSwapIf true 1 1
  | _ => next

end TvmLean
