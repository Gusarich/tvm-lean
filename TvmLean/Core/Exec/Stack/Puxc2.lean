import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPuxc2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .puxc2 x y z =>
      let st ← get
      if x < st.stack.size && 1 < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 2
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | _ => next

end TvmLean
