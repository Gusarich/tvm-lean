import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetBool (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retBool =>
      if (← VM.popBool) then
        VM.ret
      else
        VM.retAlt
  | _ => next

end TvmLean
