import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvLdGrams (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldGrams =>
      let csr0 ← VM.popSlice
      let (len, csr1) ← csr0.takeBitsAsNatCellUnd 4
      let dataBits : Nat := len * 8
      if csr1.haveBits dataBits then
        let bs := csr1.readBits dataBits
        let n : Nat := bitsToNat bs
        VM.pushIntQuiet (.num (Int.ofNat n)) false
        VM.push (.slice (csr1.advanceBits dataBits))
      else
        throw .cellUnd
  | _ => next

end TvmLean
