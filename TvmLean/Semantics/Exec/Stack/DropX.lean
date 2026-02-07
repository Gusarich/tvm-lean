import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackDropX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dropX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        let keep : Nat := st.stack.size - x
        set { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | _ => next

end TvmLean
