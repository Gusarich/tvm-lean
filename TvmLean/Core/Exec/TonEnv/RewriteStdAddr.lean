import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRewriteStdAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.rewriteStdAddr quiet) =>
      let csr0 ← VM.popSlice
      let parsed : Except Excno (Int × Nat) := do
        let (tag, s2) ← csr0.takeBitsAsNatCellUnd 2
        if tag != 2 then
          throw .cellUnd
        let s3 ← s2.skipMaybeAnycast
        let (wcNat, sWc) ← s3.takeBitsAsNatCellUnd 8
        if !sWc.haveBits 256 then
          throw .cellUnd
        let addrBits := sWc.readBits 256
        let sEnd := sWc.advanceBits 256
        if sEnd.bitsRemaining != 0 || sEnd.refsRemaining != 0 then
          throw .cellUnd
        let wc : Int := natToIntSignedTwos wcNat 8
        let addr : Nat := bitsToNat addrBits
        return (wc, addr)
      match parsed with
      | .ok (wc, addr) =>
          VM.pushSmallInt wc
          VM.pushIntQuiet (.num (Int.ofNat addr)) false
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw e
  | _ => next

end TvmLean
