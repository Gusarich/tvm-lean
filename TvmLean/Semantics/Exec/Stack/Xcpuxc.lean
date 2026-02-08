import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXcpuxc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xcpuxc x y z =>
      let st ← get
      if decide (st.stack.size > Nat.max (Nat.max x y) 1 ∧ z ≤ st.stack.size) then
        VM.swap 1 x
        let v ← VM.fetch y
        VM.push v
        VM.swap 0 1
        VM.swap 0 z
      else
        throw .stkUnd
  | _ => next

end TvmLean
