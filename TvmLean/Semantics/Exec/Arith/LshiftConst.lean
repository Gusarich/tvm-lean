import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n => VM.pushIntQuiet (.num (n * intPow2 bits)) quiet
  | _ => next

end TvmLean
