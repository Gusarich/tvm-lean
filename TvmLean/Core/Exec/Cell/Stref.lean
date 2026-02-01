import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stref =>
      -- Stack: ... cell builder -- ...  (builder on top)
      let b ← VM.popBuilder
      let c ← VM.popCell
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
      else
        throw .cellOv
  | _ => next

end TvmLean
