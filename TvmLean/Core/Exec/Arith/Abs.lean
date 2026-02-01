import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithAbs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .abs quiet =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n =>
          if n < 0 then
            VM.pushIntQuiet (.num (-n)) quiet
          else
            VM.pushIntQuiet (.num n) quiet
  | _ => next

end TvmLean
