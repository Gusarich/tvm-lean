import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpBchk (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .bchk needBits needRefs quiet =>
      let refs : Nat ← if needRefs then VM.popNatUpTo 7 else pure 0
      let bits : Nat ← if needBits then VM.popNatUpTo 1023 else pure 0
      let b ← VM.popBuilder
      let ok : Bool := b.canExtendBy bits refs
      if quiet then
        VM.pushSmallInt (if ok then -1 else 0)
      else if !ok then
        throw .cellOv
      else
        pure ()
  | _ => next

end TvmLean
