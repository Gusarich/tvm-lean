import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQdec (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qdec =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.dec) true
  | _ => next

end TvmLean
