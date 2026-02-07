import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackTuck (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tuck =>
      VM.swap 0 1
      let v ← VM.fetch 1
      VM.push v
  | _ => next

end TvmLean
