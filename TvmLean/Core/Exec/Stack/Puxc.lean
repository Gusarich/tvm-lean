import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPuxc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .puxc x y =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
      else
        throw .stkUnd
  | _ => next

end TvmLean
