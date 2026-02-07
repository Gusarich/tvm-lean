import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxArgs params retVals =>
      let cont ← VM.popCont
      VM.call cont (Int.ofNat params) retVals
  | _ => next

end TvmLean
