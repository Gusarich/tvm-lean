import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackChkDepth (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .chkDepth =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        pure ()
      else
        throw .stkUnd
  | _ => next

end TvmLean
