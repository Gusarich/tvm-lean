import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSbits (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sbits =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
  | _ => next

end TvmLean
