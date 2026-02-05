import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpxVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpxVarArgs =>
      -- Mirrors C++ `exec_jmpx_varargs`: pop `params ∈ [-1..254]`, then jump to continuation with `pass_args=params`.
      let params ← VM.popIntFinite
      if decide (params < -1 ∨ params > 254) then
        throw .rangeChk
      let cont ← VM.popCont
      VM.jump cont params
  | _ => next

end TvmLean

