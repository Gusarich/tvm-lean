import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetGlob (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.getGlob idx) =>
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | _ => next

end TvmLean
