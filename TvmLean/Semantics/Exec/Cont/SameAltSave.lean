import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSameAltSave (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sameAltSave =>
      -- Mirrors `SAMEALTSAVE` from `crypto/vm/contops.cpp` (`exec_samealt(save=true)`):
      -- define `c1` inside `c0` (if absent), then set `c1 := c0`.
      let st ← get
      let c1Old : Continuation := st.regs.c1
      let c0' : Continuation := st.regs.c0.defineC1 c1Old
      set { st with regs := { st.regs with c0 := c0', c1 := c0' } }
  | _ => next

end TvmLean
