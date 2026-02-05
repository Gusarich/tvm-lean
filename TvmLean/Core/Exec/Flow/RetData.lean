import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetData (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retData =>
      -- Mirrors C++ `exec_ret_data`: push remaining code slice and return.
      VM.pushCode
      VM.ret
  | _ => next

end TvmLean
