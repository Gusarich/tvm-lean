import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithPushNull (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushNull =>
      VM.push .null
  | _ => next

end TvmLean
