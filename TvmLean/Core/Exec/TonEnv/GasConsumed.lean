import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGasConsumed (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .gasConsumed =>
      let st ← get
      VM.pushSmallInt st.gas.gasConsumed
  | _ => next

end TvmLean
