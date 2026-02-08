import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvCommit (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .commit =>
      let st ← get
      if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
        set { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } }
      else
        throw .cellOv
  | _ => next

end TvmLean
