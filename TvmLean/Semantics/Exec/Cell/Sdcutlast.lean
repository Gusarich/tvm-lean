import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdcutlast (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdcutlast =>
      VM.checkUnderflow 2
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let drop : Nat := s.bitsRemaining - bits
        let fromPos : Nat := s.bitPos + drop
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract fromPos (fromPos + bits))
            #[]
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | _ => next

end TvmLean
