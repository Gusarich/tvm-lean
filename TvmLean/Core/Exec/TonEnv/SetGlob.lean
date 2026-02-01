import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvSetGlob (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.setGlob idx) =>
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | _ => next

end TvmLean
