import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullSwapIfNot2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullSwapIfNot2 =>
      VM.execNullSwapIf false 0 2
  | _ => next

end TvmLean
