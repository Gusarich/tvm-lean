import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callRef code =>
      VM.registerCellLoad code.cell
      modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
