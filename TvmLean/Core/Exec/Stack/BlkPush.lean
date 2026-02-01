import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackBlkPush (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .blkPush x y =>
      let st ← get
      if y < st.stack.size then
        for _ in [0:x] do
          let v ← VM.fetch y
          VM.push v
      else
        throw .stkUnd
  | _ => next

end TvmLean
