import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithEqual (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .equal =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.equalResult y) false
  | _ => next

end TvmLean
