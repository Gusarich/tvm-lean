import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvConfigDict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .configDict =>
      -- Mirrors C++ `exec_get_config_dict` (tonops.cpp).
      VM.pushC7Param 9
      VM.pushSmallInt 32
  | _ => next

end TvmLean

