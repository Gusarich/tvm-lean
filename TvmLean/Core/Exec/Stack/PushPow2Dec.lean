import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPushPow2Dec (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushPow2Dec exp =>
      VM.pushIntQuiet (.num (intPow2 exp - 1)) false
  | _ => next

end TvmLean
