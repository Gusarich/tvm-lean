import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfrefElseRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifrefElseRef t f =>
      let selected : Slice := if (← VM.popBool) then t else f
      VM.registerCellLoad selected.cell
      -- C++ `st->call(st->ref_to_cont(cell))`: load cost is charged before special-cell rejection.
      if selected.cell.special then
        throw .cellUnd
      VM.call (.ordinary selected (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
