import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQsub (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qsub =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.sub y) true
  | _ => next

end TvmLean

