import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXc2pu (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xc2pu x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
        let v ← VM.fetch z
        VM.push v
      else
        throw .stkUnd
  | _ => next

end TvmLean
