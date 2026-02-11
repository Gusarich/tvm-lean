import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpRef code =>
      VM.registerCellLoad code.cell
      -- C++ `ref_to_cont(load_cell_slice_ref)` rejects special/exotic cells after load registration.
      if code.cell.special then
        throw .cellUnd
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .jmpRefData code =>
      VM.registerCellLoad code.cell
      -- C++ `exec_do_with_ref` builds `cont = ref_to_cont(cell)` before the JMPREFDATA lambda
      -- runs, so special/exotic rejection must happen before `push_code()`.
      if code.cell.special then
        throw .cellUnd
      VM.pushCode
      VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | _ => next

end TvmLean
