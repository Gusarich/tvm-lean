import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallDict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callDict idx =>
      VM.pushSmallInt (Int.ofNat idx)
      let st ← get
      VM.call st.regs.c3
  | _ => next

end TvmLean
