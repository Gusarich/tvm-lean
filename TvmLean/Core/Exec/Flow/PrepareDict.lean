import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPrepareDict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .prepareDict idx =>
      -- Matches C++ `exec_preparedict` (contops.cpp).
      VM.pushSmallInt (Int.ofNat idx)
      let st ← get
      VM.push (.cont st.regs.c3)
  | _ => next

end TvmLean
