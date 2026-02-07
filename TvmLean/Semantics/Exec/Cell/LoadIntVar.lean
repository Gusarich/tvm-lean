import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellLoadIntVar (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .loadIntVar unsigned prefetch quiet =>
      VM.checkUnderflow 2
      -- Stack effect: ... slice bits -- ...
      -- Bits may be 0..257 for signed, 0..256 for unsigned (per C++ pop_smallint_range).
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
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
