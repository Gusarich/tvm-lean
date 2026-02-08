import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQsubr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qsubr =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (y.sub x) true
  | _ => next

end TvmLean
