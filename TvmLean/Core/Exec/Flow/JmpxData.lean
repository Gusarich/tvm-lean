import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpxData (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpxData =>
      let cont ← VM.popCont
      VM.pushCode
      VM.jump cont
  | _ => next

end TvmLean

