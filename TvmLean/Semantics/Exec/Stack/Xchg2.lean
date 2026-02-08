import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchg2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchg2 x y =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
      else
        throw .stkUnd
  | _ => next

end TvmLean
