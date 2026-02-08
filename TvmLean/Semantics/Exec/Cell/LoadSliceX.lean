import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLoadSliceX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .loadSliceX prefetch quiet =>
      VM.checkUnderflow 2
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let subBits := s.readBits bits
        let subCell : Cell := Cell.mkOrdinary subBits #[]
        VM.push (.slice (Slice.ofCell subCell))
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | _ => next

end TvmLean
