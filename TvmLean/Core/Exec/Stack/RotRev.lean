import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackRotRev (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rotRev =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 0 1
        VM.swap 1 2
      else
        throw .stkUnd
  | _ => next

end TvmLean
