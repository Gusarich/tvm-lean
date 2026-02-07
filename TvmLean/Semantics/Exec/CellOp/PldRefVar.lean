import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpPldRefVar (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .pldRefVar =>
      VM.checkUnderflow 2
      let idx ← VM.popNatUpTo 3
      let s ← VM.popSlice
      if s.haveRefs (idx + 1) then
        VM.push (.cell (s.cell.refs[s.refPos + idx]!))
      else
        throw .cellUnd
  | _ => next

end TvmLean
