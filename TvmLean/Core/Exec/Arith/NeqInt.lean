import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNeqInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .neqInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a ≠ y then -1 else 0)
  | _ => next

end TvmLean
