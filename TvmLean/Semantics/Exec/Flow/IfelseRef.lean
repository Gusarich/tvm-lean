import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfelseRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifelseRef code =>
      VM.checkUnderflow 2
      let cont ← VM.popCont
      if (← VM.popBool) then
        VM.call cont
      else
        VM.registerCellLoad code.cell
        VM.call (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
