import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchg (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchg x y =>
      if decide (x = 0 ∨ y ≤ x) then
        throw .invOpcode
      let st ← get
      if y < st.stack.size then
        VM.swap x y
      else
        throw .stkUnd
  | _ => next

end TvmLean
