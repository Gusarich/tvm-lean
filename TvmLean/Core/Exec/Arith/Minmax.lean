import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMinmax (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .minmax =>
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b =>
          if a ≤ b then
            VM.pushIntQuiet (.num a) false
            VM.pushIntQuiet (.num b) false
          else
            VM.pushIntQuiet (.num b) false
            VM.pushIntQuiet (.num a) false
      | _, _ =>
          VM.pushIntQuiet .nan false
          VM.pushIntQuiet .nan false
  | _ => next

end TvmLean
