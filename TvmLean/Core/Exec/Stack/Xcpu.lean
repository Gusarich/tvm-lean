import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXcpu (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xcpu x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        VM.swap 0 x
        let v ← VM.fetch y
        VM.push v
      else
        throw .stkUnd
  | _ => next

end TvmLean
