import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMin (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .min =>
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b => VM.pushIntQuiet (.num (if a ≤ b then a else b)) false
      | _, _ => VM.pushIntQuiet .nan false
  | _ => next

end TvmLean
