import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithDec (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dec =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.dec) false
  | _ => next

end TvmLean
