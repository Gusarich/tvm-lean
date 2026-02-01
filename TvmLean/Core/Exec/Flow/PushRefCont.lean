import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRefCont (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRefCont c =>
      modify fun st => st.registerCellLoad c
      VM.push (.cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty))
  | _ => next

end TvmLean
