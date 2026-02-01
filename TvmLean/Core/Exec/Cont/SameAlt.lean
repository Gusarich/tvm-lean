import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSameAlt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sameAlt =>
      modify fun st => { st with regs := { st.regs with c1 := st.regs.c0 } }
  | _ => next

end TvmLean
