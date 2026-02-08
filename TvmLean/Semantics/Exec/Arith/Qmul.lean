import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQmul (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qmul =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.mul y) true
  | _ => next

end TvmLean
