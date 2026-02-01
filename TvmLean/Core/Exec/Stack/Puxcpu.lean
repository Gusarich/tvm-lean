import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPuxcpu (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .puxcpu x y z =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
        let v2 ← VM.fetch z
        VM.push v2
      else
        throw .stkUnd
  | _ => next

end TvmLean
