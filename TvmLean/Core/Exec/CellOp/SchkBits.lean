import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSchkBits (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .schkBits quiet =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      let ok : Bool := s.haveBits bits
      if quiet then
        VM.pushSmallInt (if ok then -1 else 0)
      else if !ok then
        throw .cellUnd
      else
        pure ()
  | _ => next

end TvmLean
