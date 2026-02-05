import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoSha256U (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp .sha256U =>
      let s ← VM.popSlice
      if s.bitsRemaining % 8 ≠ 0 then
        throw .cellUnd
      let bytes : Array UInt8 := bitStringToBytesBE (s.readBits s.bitsRemaining)
      let digest : ByteArray := hashSha256 (ByteArray.mk bytes)
      let n : Nat := byteArrayToNatBE digest
      VM.push (.int (.num (Int.ofNat n)))
  | _ => next

end TvmLean

