import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRefSlice (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRefSlice c =>
      -- Matches C++ `exec_push_ref` (cellops.cpp), mode 1: load cell slice (charges cell load).
      modify fun st => st.registerCellLoad c
      -- `load_cell_slice_ref` charges before it rejects exotic/special cells.
      if c.special then
        throw .cellUnd
      VM.push (.slice (Slice.ofCell c))
  | _ => next

end TvmLean
