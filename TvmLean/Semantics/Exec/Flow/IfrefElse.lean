import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfrefElse (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifrefElse code =>
      VM.checkUnderflow 2
      let cont ← VM.popCont
      if (← VM.popBool) then
        VM.registerCellLoad code.cell
        VM.call (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        VM.call cont
  | _ => next

end TvmLean
