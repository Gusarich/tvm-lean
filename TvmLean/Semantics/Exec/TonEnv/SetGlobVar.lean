import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvSetGlobVar (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .setGlobVar =>
      -- Match C++: check stack underflow before decoding index from the stack.
      VM.checkUnderflow 2
      let idx ← VM.popNatUpTo 254
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | _ => next

end TvmLean
