import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPu2xc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pu2xc x y z =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size + 1 then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        let v2 ← VM.fetch y
        VM.push v2
        VM.swap 0 1
        VM.swap 0 z
      else
        throw .stkUnd
  | _ => next

end TvmLean
