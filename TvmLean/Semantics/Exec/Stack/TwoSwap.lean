import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackTwoSwap (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .twoSwap =>
      let st ← get
      if 3 < st.stack.size then
        VM.swap 1 3
        VM.swap 0 2
      else
        throw .stkUnd
  | _ => next

end TvmLean
