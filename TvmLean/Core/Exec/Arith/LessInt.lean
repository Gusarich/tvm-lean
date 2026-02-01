import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLessInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lessInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a < y then -1 else 0)
  | _ => next

end TvmLean
