import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfnotjmp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifnotjmp =>
      VM.checkUnderflow 2
      let cont ← VM.popCont
      if !(← VM.popBool) then
        modify fun st => st.jumpTo cont
      else
        pure ()
  | _ => next

end TvmLean
