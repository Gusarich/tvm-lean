import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNeq (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .neq =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a ≠ b then -1 else 0)
  | _ => next

end TvmLean
