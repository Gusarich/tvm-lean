import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithSgn (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sgn =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n =>
          if n < 0 then
            VM.pushSmallInt (-1)
          else if n = 0 then
            VM.pushSmallInt 0
          else
            VM.pushSmallInt 1
  | _ => next

end TvmLean
