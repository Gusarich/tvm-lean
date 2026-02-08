import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRandu256 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .randu256 =>
      let y ← VM.generateRandu256
      VM.pushIntQuiet (.num y) false
  | _ => next

end TvmLean
