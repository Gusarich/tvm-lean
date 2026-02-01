import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithAddInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .addInt n =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a => VM.pushIntQuiet (.num (a + n)) false
  | _ => next

end TvmLean
