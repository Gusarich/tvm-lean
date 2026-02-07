import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQnegate (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qnegate =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan true
      | .num n => VM.pushIntQuiet (.num (-n)) true
  | _ => next

end TvmLean
