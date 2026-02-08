import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullRotrIf2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullRotrIf2 =>
      VM.execNullSwapIf true 1 2
  | _ => next

end TvmLean
