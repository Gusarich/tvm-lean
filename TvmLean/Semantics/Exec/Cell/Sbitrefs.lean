import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSbitrefs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sbitrefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | _ => next

end TvmLean
