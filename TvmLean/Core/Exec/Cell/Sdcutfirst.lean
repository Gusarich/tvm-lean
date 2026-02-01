import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdcutfirst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdcutfirst =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + bits))
            (s.cell.refs.extract s.refPos s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | _ => next

end TvmLean
