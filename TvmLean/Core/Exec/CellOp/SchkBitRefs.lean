import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSchkBitRefs (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .schkBitRefs quiet =>
      VM.checkUnderflow 3
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      let ok : Bool := s.haveBits bits && s.haveRefs refs
      if quiet then
        VM.pushSmallInt (if ok then -1 else 0)
      else if !ok then
        throw .cellUnd
      else
        pure ()
  | _ => next

end TvmLean
