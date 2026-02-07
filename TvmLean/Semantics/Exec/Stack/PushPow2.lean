import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPushPow2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushPow2 exp =>
      -- Match C++ `exec_push_pow2`: push raw integer value (can be 2^256).
      VM.push (.int (.num (intPow2 exp)))
  | _ => next

end TvmLean
