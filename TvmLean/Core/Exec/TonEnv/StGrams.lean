import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvStGrams (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stGrams =>
      -- Mirrors `util::store_var_integer` (len_bits=4, unsigned) used by `STGRAMS`.
      -- Stack: ... builder x -- ...
      let x ← VM.popInt
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if n < 0 then
            throw .rangeChk
          let b ← VM.popBuilder
          let bitsLen : Nat := natLenBits n.toNat
          let lenBytes : Nat := (bitsLen + 7) / 8
          if lenBytes ≥ 16 then
            throw .rangeChk
          let totalBits : Nat := 4 + lenBytes * 8
          if !b.canExtendBy totalBits then
            throw .cellOv
          let bs := natToBits lenBytes 4 ++ natToBits n.toNat (lenBytes * 8)
          VM.push (.builder (b.storeBits bs))
  | _ => next

end TvmLean
