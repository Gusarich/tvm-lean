import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpRef code =>
      modify fun st => st.registerCellLoad code.cell
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .jmpRefData code =>
      modify fun st => st.registerCellLoad code.cell
      VM.pushCode
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean

