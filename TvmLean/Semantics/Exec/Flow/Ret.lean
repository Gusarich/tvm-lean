import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRet (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ret =>
      VM.ret
  | _ => next

end TvmLean
