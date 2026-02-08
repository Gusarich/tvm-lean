import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQmax (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qmax =>
      VM.checkUnderflow 2
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b => VM.pushIntQuiet (.num (if a ≤ b then b else a)) true
      | _, _ => VM.pushIntQuiet .nan true
  | _ => next

end TvmLean
