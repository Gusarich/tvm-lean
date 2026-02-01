import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushCont (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushCont code =>
      VM.push (.cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty))
  | _ => next

end TvmLean
