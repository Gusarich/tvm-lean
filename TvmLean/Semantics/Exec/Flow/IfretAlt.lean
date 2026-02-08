import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfretAlt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt .ifretAlt =>
      if (← VM.popBool) then
        VM.retAlt
      else
        pure ()
  | .contExt .ifnotretAlt =>
      if !(← VM.popBool) then
        VM.retAlt
      else
        pure ()
  | _ => next

end TvmLean
