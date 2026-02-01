import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullSwapIf2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullSwapIf2 =>
      VM.execNullSwapIf true 0 2
  | _ => next

end TvmLean
