import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPush3 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .push3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
        let v3 ← VM.fetch (z + 2)
        VM.push v3
      else
        throw .stkUnd
  | _ => next

end TvmLean
