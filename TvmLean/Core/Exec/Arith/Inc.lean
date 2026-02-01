import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithInc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .inc =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.inc) false
  | _ => next

end TvmLean
