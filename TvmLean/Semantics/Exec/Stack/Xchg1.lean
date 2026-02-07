import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchg1 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchg1 idx =>
      VM.swap 1 idx
  | _ => next

end TvmLean
