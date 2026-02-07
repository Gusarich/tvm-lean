import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retVarArgs =>
      -- Mirrors C++ `exec_ret_varargs`: pop `retvals ∈ [-1..254]` and `RET` with `passArgs=retvals`.
      let retvals ← VM.popIntFinite
      if decide (retvals < -1 ∨ retvals > 254) then
        throw .rangeChk
      VM.ret retvals
  | _ => next

end TvmLean

