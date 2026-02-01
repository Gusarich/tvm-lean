import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithRshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n bits)) quiet
  | _ => next

end TvmLean
