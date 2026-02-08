import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackTwoDup (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .twoDup =>
      let st ← get
      if 1 < st.stack.size then
        let v1 ← VM.fetch 1
        VM.push v1
        let v2 ← VM.fetch 1
        VM.push v2
      else
        throw .stkUnd
  | _ => next

end TvmLean
