import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellBbits (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .bbits =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat b.bits.size)
  | _ => next

end TvmLean
