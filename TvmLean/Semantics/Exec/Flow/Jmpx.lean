import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpx =>
      let cont ← VM.popCont
      VM.jump cont
  | _ => next

end TvmLean
