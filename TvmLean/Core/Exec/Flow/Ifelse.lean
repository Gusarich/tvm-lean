import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfelse (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifelse =>
      VM.checkUnderflow 3
      let cont0 ← VM.popCont
      let cont1 ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont1
      else
        modify fun st => st.callTo cont0
  | _ => next

end TvmLean
