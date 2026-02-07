import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellNewc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .newc =>
      VM.push (.builder Builder.empty)
  | _ => next

end TvmLean
