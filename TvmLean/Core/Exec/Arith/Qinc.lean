import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQinc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qinc =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.inc) true
  | _ => next

end TvmLean
