import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchg3 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchg3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 2
      if need < st.stack.size then
        VM.swap 2 x
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | _ => next

end TvmLean
