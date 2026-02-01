import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvAccept (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .accept =>
      let st ← get
      -- C++: change gas limit to GasLimits::infty.
      let st' := { st with gas := st.gas.changeLimit GasLimits.infty }
      set st'
  | _ => next

end TvmLean
