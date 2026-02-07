import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithSub (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sub =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.sub y) false
  | _ => next

end TvmLean
