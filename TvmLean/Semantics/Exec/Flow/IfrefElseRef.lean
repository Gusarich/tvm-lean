import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfrefElseRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifrefElseRef t f =>
      if (← VM.popBool) then
        VM.registerCellLoad t.cell
        modify fun st => st.callTo (.ordinary t (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        VM.registerCellLoad f.cell
        modify fun st => st.callTo (.ordinary f (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
