import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullSwapIf (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullSwapIf =>
      VM.execNullSwapIf true 0 1
  | _ => next

end TvmLean
