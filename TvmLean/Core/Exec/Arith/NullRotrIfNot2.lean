import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullRotrIfNot2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullRotrIfNot2 =>
      VM.execNullSwapIf false 1 2
  | _ => next

end TvmLean
