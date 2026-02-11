import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowIfref (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ifref code =>
      if (← VM.popBool) then
        VM.registerCellLoad code.cell
        VM.call (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | _ => next

end TvmLean
