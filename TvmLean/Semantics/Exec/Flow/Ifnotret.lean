import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfnotret (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifnotret =>
      if !(← VM.popBool) then
        VM.ret
      else
        pure ()
  | _ => next

end TvmLean
