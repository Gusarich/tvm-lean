import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIf (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .if_ =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont
      else
        pure ()
  | _ => next

end TvmLean
