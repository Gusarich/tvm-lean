import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNegate (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .negate =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n => VM.pushIntQuiet (.num (-n)) false
  | _ => next

end TvmLean
