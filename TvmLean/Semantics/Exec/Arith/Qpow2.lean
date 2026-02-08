import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQpow2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qpow2 =>
      let exp ← VM.popNatUpTo 1023
      VM.pushIntQuiet (.num (intPow2 exp)) true
  | _ => next

end TvmLean
