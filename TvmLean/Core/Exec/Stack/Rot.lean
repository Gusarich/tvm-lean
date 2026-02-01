import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackRot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rot =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 1 2
        VM.swap 0 1
      else
        throw .stkUnd
  | _ => next

end TvmLean
