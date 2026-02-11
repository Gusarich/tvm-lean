import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSaveCtr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .saveCtr idxRaw =>
      -- Mirrors `SAVECTR c<idx>` from `crypto/vm/contops.cpp` (`exec_save_ctr`):
      -- define `c<idx>` inside the current return continuation `c0`.
      --
      -- C++ masks the opcode arg (`idx = args & 15`) and then feeds `st->get(idx)`
      -- into `define`. Invalid masked indices become `type_chk` (not `range_chk`)
      -- because `get(idx)` is an empty stack entry.
      let idx := idxRaw &&& 0xf
      let st ← get
      let v : Value :=
        match idx with
        | 0 => .cont st.regs.c0
        | 1 => .cont st.regs.c1
        | 2 => .cont st.regs.c2
        | 3 => .cont st.regs.c3
        | 4 => .cell st.regs.c4
        | 5 => .cell st.regs.c5
        | 7 => .tuple st.regs.c7
        | _ => .null
      let c0 ←
        match st.regs.c0.defineCtr idx v with
        | .ok k => pure k
        | .error e => throw e
      set { st with regs := { st.regs with c0 := c0 } }
  | _ => next

end TvmLean
