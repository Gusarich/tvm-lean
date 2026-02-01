import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPush (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .push idx =>
      let v ← VM.fetch idx
      VM.push v
  | _ => next

end TvmLean
