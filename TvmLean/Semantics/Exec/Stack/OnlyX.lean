import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackOnlyX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .onlyX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        set { st with stack := st.stack.take x }
      else
        throw .stkUnd
  | _ => next

end TvmLean
