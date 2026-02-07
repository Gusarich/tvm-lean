import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxVarArgs =>
      -- Mirrors C++ `exec_callx_varargs`: pop `retvals`, `params` (both in [-1..254]) and call the continuation.
      VM.checkUnderflow 3
      let retVals ← VM.popIntFinite
      if decide (retVals < -1 ∨ retVals > 254) then
        throw .rangeChk
      let params ← VM.popIntFinite
      if decide (params < -1 ∨ params > 254) then
        throw .rangeChk
      let cont ← VM.popCont
      VM.call cont params retVals
  | _ => next

end TvmLean
