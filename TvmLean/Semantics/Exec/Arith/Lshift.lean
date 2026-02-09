import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithLshift (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lshift =>
      VM.checkUnderflow 2
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      if shift ≥ 260 then
        VM.pushIntQuiet .nan false
      else
        match x with
        | .nan => VM.pushIntQuiet .nan false
        | .num n => VM.pushIntQuiet (.num (n * intPow2 shift)) false
  | _ => next

end TvmLean
