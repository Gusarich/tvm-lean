import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowExecute (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .execute =>
      let cont ← VM.popCont
      VM.call cont
  | _ => next

end TvmLean
