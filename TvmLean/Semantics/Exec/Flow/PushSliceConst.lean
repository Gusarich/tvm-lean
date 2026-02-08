import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushSliceConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushSliceConst s =>
      VM.push (.slice s)
  | _ => next

end TvmLean
