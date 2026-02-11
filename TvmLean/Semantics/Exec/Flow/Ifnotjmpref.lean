import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfnotjmpref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifnotjmpref code =>
      if !(← VM.popBool) then
        VM.registerCellLoad code.cell
        -- C++ `ref_to_cont(load_cell_slice_ref)` rejects special/exotic cells after charging load gas.
        if code.cell.special then
          throw .cellUnd
        VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | _ => next

end TvmLean
