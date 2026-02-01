import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithIsNull (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .isNull =>
      let v ← VM.pop
      match v with
      | .null => VM.pushSmallInt (-1)
      | _ => VM.pushSmallInt 0
  | _ => next

end TvmLean
