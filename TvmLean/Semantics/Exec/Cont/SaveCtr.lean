import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSaveCtr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .saveCtr _idx =>
      -- Mirrors `SAVECTR c<idx>` from `crypto/vm/contops.cpp` (`exec_save_ctr`):
      -- define `c<idx>` inside the current return continuation `c0`.
      --
      let st ← get
      let v : Value ←
        match st.getCtr _idx with
        | .ok v => pure v
        | .error e => throw e
      let c0 ←
        match st.regs.c0.defineCtr _idx v with
        | .ok k => pure k
        | .error e => throw e
      set { st with regs := { st.regs with c0 := c0 } }
  | _ => next

end TvmLean
