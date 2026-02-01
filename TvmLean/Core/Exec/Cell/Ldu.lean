import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLdu (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldu bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n := bitsToNat bs
        VM.push (.int (.num (Int.ofNat n)))
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | _ => next

end TvmLean
