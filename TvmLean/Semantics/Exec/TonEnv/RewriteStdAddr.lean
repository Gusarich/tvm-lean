import TvmLean.Semantics.Exec.Common

namespace TvmLean

def rewriteMessageAddr256 (addr : Slice) (pfxVal : Value) : Except Excno Nat := do
  if addr.bitsRemaining != 256 then
    throw .cellUnd
  let addrBits := addr.readBits 256
  match pfxVal with
  | .null =>
      return bitsToNat addrBits
  | .slice pfx =>
      let pLen : Nat := pfx.bitsRemaining
      if pLen = 0 then
        return bitsToNat addrBits
      if pLen > 256 then
        throw .cellUnd
      let pBits := pfx.readBits pLen
      let newBits := pBits ++ addrBits.drop pLen
      return bitsToNat newBits
  | _ =>
      throw .cellUnd

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRewriteStdAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.rewriteStdAddr quiet) =>
      let csr0 ← VM.popSlice
      let parsed : Except Excno (Int × Nat) := do
        let (tup, rest) ← csr0.parseMessageAddr
        if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then
          throw .cellUnd
        if tup.size != 4 then
          throw .cellUnd
        match tup[0]!, tup[1]!, tup[2]!, tup[3]! with
        | .int (.num t), pfxVal, .int (.num wc), .slice addr =>
            if t != 2 && t != 3 then
              throw .cellUnd
            let hash ← rewriteMessageAddr256 addr pfxVal
            return (wc, hash)
        | _, _, _, _ =>
            throw .cellUnd
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
