import TvmLean.Core.Exec.Common

namespace TvmLean

def rewriteMessageAddr (addr : Slice) (pfxVal : Value) : Except Excno Slice := do
  match pfxVal with
  | .null =>
      return addr
  | .slice pfx =>
      let pLen : Nat := pfx.bitsRemaining
      if pLen = 0 then
        return addr
      let aLen : Nat := addr.bitsRemaining
      if pLen > aLen then
        throw .cellUnd
      if pLen = aLen then
        return pfx
      let pBits := pfx.readBits pLen
      let aBits := addr.readBits aLen
      let newBits := pBits ++ aBits.drop pLen
      return Slice.ofCell (Cell.mkOrdinary newBits #[])
  | _ =>
      throw .cellUnd

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRewriteVarAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.rewriteVarAddr quiet) =>
      let csr0 ← VM.popSlice
      let parsed : Except Excno (Int × Slice) := do
        let (tup, rest) ← csr0.parseMessageAddr
        if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then
          throw .cellUnd
        if tup.size != 4 then
          throw .cellUnd
        match tup[0]!, tup[1]!, tup[2]!, tup[3]! with
        | .int (.num t), pfxVal, .int (.num wc), .slice addr =>
            if t != 2 && t != 3 then
              throw .cellUnd
            let addr' ← rewriteMessageAddr addr pfxVal
            return (wc, addr')
        | _, _, _, _ =>
            throw .cellUnd
      match parsed with
      | .ok (wc, addr) =>
          VM.pushSmallInt wc
          VM.push (.slice addr)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw e
  | _ => next

end TvmLean
