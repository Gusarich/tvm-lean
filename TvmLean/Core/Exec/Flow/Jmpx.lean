import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpx =>
      let cont ← VM.popCont
      modify fun st => st.jumpTo cont
  | _ => next

end TvmLean
