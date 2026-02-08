import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoChkSignU (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp .chkSignU =>
      VM.checkUnderflow 3
      let key ← VM.popInt
      let sigSlice ← VM.popSlice
      let hash ← VM.popInt

      let msgBytes ←
        match exportUInt256BE hash with
        | .ok bs => pure bs
        | .error e => throw e
      let sigBytes ←
        match sigSlice.prefetchBytesCellUnd 64 with
        | .ok bs => pure bs
        | .error e => throw e
      let keyBytes ←
        match exportUInt256BE key with
        | .ok bs => pure bs
        | .error e => throw e

      modify fun st => st.registerChkSgnCall
      let ok := host.ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | _ => next

end TvmLean
