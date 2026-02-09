import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMax (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .max =>
      VM.checkUnderflow 2
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b => VM.pushIntQuiet (.num (if a ≤ b then b else a)) false
      | _, _ => VM.pushIntQuiet .nan false
  | _ => next

end TvmLean
