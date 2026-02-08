import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPushNegPow2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushNegPow2 exp =>
      VM.pushIntQuiet (.num (-intPow2 exp)) false
  | _ => next

end TvmLean
