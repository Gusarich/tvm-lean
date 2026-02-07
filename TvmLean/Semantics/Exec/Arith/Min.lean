import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMin (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .min =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.min y) false
  | _ => next

end TvmLean
