import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXcpu2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xcpu2 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        VM.swap 0 x
        let v1 ← VM.fetch y
        VM.push v1
        let v2 ← VM.fetch (z + 1)
        VM.push v2
      else
        throw .stkUnd
  | _ => next

end TvmLean
