import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetAlt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retAlt =>
      VM.retAlt
  | _ => next

end TvmLean
