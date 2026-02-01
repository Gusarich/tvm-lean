import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackXchgX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xchgX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        VM.swap 0 x
      else
        throw .stkUnd
  | _ => next

end TvmLean
