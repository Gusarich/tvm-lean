import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellCtos (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ctos =>
      let c ← VM.popCell
      -- C++ `CTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      -- `load_cell_slice_ref` charges before it rejects exotic/special cells.
      if c.special then
        throw .cellUnd
      VM.push (.slice (Slice.ofCell c))
  | _ => next

end TvmLean
