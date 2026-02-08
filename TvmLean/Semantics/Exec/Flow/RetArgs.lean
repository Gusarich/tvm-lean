import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retArgs n =>
      VM.ret (Int.ofNat n)
  | _ => next

end TvmLean
