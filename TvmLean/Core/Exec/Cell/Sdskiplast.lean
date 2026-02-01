import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdskiplast (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdskiplast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let keep : Nat := s.bitsRemaining - bits
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + keep))
            (s.cell.refs.extract s.refPos s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | _ => next

end TvmLean
