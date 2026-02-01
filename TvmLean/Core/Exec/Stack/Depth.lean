import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackDepth (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .depth =>
      let st ← get
      VM.pushSmallInt (Int.ofNat st.stack.size)
  | _ => next

end TvmLean
