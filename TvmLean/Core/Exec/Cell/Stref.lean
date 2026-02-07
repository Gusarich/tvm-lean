import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stref =>
      -- Stack: ... cell builder -- ...  (builder on top)
      VM.checkUnderflow 2
      let b ← VM.popBuilder
      let c ← VM.popCell
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
      else
        throw .cellOv
  | .strefq =>
      -- Stack: ... cell builder -- ...  (builder on top)
      VM.checkUnderflow 2
      let b ← VM.popBuilder
      let c ← VM.popCell
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
        VM.pushSmallInt 0
      else
        VM.push (.cell c)
        VM.push (.builder b)
        VM.pushSmallInt (-1)
  | _ => next

end TvmLean
