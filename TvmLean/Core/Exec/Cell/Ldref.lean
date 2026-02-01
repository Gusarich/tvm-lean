import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLdref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldref =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        VM.push (.cell c)
        VM.push (.slice { s with refPos := s.refPos + 1 })
      else
        throw .cellUnd
  | _ => next

end TvmLean
