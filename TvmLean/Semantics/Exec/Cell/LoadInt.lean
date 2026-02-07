import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLoadInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .loadInt unsigned prefetch quiet bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n : Int :=
          if unsigned then
            Int.ofNat (bitsToNat bs)
          else
            bitsToIntSignedTwos bs
        VM.pushIntQuiet (.num n) false
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
