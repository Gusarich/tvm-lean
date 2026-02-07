import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellCdepth (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cdepth =>
      let c ← VM.popMaybeCell
      match c with
      | none => VM.pushSmallInt 0
      | some cell => VM.pushSmallInt (Int.ofNat cell.depth)
  | _ => next

end TvmLean
