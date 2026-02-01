import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLdrefRtos (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldrefRtos =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        let s' := { s with refPos := s.refPos + 1 }
        -- C++ `LDREFRTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
        modify fun st => st.registerCellLoad c
        VM.push (.slice s')
        VM.push (.slice (Slice.ofCell c))
      else
        throw .cellUnd
  | _ => next

end TvmLean
