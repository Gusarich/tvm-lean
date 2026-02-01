import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchg0 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchg0 idx =>
      VM.swap 0 idx
  | _ => next

end TvmLean
