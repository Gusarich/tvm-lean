import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfnotjmpref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifnotjmpref code =>
      if !(← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.jumpTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | _ => next

end TvmLean
