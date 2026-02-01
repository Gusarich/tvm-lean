import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellXctos (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xctos =>
      let c ← VM.popCell
      -- C++ `XCTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
      -- C++ `XCTOS` also returns a boolean `is_special` (true for exotic/special cells).
      VM.pushSmallInt (if c.special then -1 else 0)
  | _ => next

end TvmLean
