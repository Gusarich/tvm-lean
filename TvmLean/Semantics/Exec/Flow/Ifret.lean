import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfret (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifret =>
      if (← VM.popBool) then
        VM.ret
      else
        pure ()
  | _ => next

end TvmLean
