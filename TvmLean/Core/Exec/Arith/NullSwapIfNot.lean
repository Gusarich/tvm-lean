import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullSwapIfNot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullSwapIfNot =>
      VM.execNullSwapIf false 0 1
  | _ => next

end TvmLean
