import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBchkBitsImm (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .bchkBitsImm bits quiet =>
      VM.checkUnderflow 1
      let b ← VM.popBuilder
      let ok : Bool := b.canExtendBy bits
      if quiet then
        VM.pushSmallInt (if ok then -1 else 0)
      else if !ok then
        throw .cellOv
      else
        pure ()
  | _ => next

end TvmLean
