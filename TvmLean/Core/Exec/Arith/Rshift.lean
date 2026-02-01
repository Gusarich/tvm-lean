import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithRshift (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rshift =>
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) false
  | _ => next

end TvmLean
