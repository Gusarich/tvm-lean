import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMul (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .mul =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.mul y) false
  | _ => next

end TvmLean
