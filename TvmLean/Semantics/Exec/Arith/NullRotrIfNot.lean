import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNullRotrIfNot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .nullRotrIfNot =>
      VM.execNullSwapIf false 1 1
  | _ => next

end TvmLean
