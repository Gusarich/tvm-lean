import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQadd (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qadd =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.add y) true
  | _ => next

end TvmLean

