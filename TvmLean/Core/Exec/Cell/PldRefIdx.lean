import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellPldRefIdx (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pldRefIdx idx =>
      let s ← VM.popSlice
      if s.haveRefs (idx + 1) then
        let pos := s.refPos + idx
        if pos < s.cell.refs.size then
          let c := s.cell.refs[pos]!
          VM.push (.cell c)
        else
          throw .cellUnd
      else
        throw .cellUnd
  | _ => next

end TvmLean
