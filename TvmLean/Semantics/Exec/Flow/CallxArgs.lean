import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxArgs params retVals =>
      -- Mirrors C++ `exec_callx_args` / `exec_callx_args_p`:
      -- pop the continuation first, then delegate all stack/closure checks
      -- and call-frame setup to `VmState::call`.
      let cont ← VM.popCont
      VM.call cont (Int.ofNat params) retVals
  | _ => next

end TvmLean
