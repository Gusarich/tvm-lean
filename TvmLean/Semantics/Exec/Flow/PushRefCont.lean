import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRefCont (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRefCont c =>
      VM.registerCellLoad c
      -- `load_cell_slice_ref` charges before it rejects exotic/special cells.
      if c.special then
        throw .cellUnd
      VM.push (.cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty))
  | _ => next

end TvmLean
