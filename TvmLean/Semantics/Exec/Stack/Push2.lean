import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPush2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .push2 x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
      else
        throw .stkUnd
  | _ => next

end TvmLean
