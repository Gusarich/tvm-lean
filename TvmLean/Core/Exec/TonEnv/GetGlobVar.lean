import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetGlobVar (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getGlobVar =>
      let idx ← VM.popNatUpTo 254
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | _ => next

end TvmLean
