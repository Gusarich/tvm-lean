import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def execLessIntCore (quiet : Bool) (y : Int) : VM Unit := do
  let x ← VM.popInt
  match x with
  | .nan => VM.pushIntQuiet .nan quiet
  | .num a =>
      VM.pushSmallInt (if a < y then -1 else 0)

set_option maxHeartbeats 1000000 in
def execInstrArithLessInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lessInt y =>
      execLessIntCore false y
  | .qlessInt y =>
      execLessIntCore true y
  | _ => next

end TvmLean
