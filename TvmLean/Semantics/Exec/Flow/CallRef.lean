import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callRef code =>
      VM.registerCellLoad code.cell
      -- C++ `CALLREF` uses `ref_to_cont(load_cell_slice_ref(ref))`:
      -- load gas is charged first, then special/exotic cells are rejected.
      if code.cell.special then
        throw .cellUnd
      VM.call (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
