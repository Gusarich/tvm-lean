import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCrypto (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .hashExt hashId0 append rev =>
      -- Mirrors C++ `exec_hash_ext` (tonops.cpp).
      -- Args: hash_id8 + rev(bit8) + append(bit9). If hash_id8 = 255, read hash_id from stack.
      -- Stack (append=false):  ... x[cnt-1] ... x[0] cnt  -- ... hash
      -- Stack (append=true):   ... builder x[cnt-1] ... x[0] cnt  -- ... builder'
      let mut hashId : Nat := hashId0
      if hashId = 255 then
        -- C++: `pop_smallint_range(254)`
        hashId := (← VM.popNatUpTo 254)

      -- C++: `cnt = pop_smallint_range(stack.depth() - 1 - append)`
      let stBeforeCnt ← get
      let depth : Nat := stBeforeCnt.stack.size
      let need : Nat := if append then 2 else 1
      if depth < need then
        throw .stkUnd
      let maxCnt : Nat := depth - need
      let cnt ← VM.popNatUpTo maxCnt

      let bytesPerGasUnit ←
        match hashId with
        | 0 => pure 33
        | 1 => pure 16
        | 2 => pure 19
        | 3 => pure 11
        | 4 => pure 6
        | _ => throw .rangeChk

      let digestSize : Nat :=
        match hashId with
        | 0 => 32
        | 3 => 32
        | 1 => 64
        | 2 => 64
        | 4 => 64
        | _ => 0

      let st0 ← get
      let stack0 := st0.stack

      let mut totalBits : Nat := 0
      let mut gasConsumed : Int := 0
      let mut acc : BitByteAcc := {}

      for i in [0:cnt] do
        let idx : Nat := if rev then i else (cnt - 1 - i)
        let entry : Value := stack0[stack0.size - 1 - idx]!

        let (bits, size) ←
          match entry with
          | .slice s => pure (s.readBits s.bitsRemaining, s.bitsRemaining)
          | .builder b => pure (b.bits, b.bits.size)
          | _ =>
              -- C++: `stack.pop_many(cnt); throw type_chk`
              modify fun st => { st with stack := st.stack.take (st.stack.size - cnt) }
              throw .typeChk

        totalBits := totalBits + size
        let gasTotal : Int :=
          (Int.ofNat (i + 1) * hashExtEntryGasPrice) +
            Int.ofNat (((totalBits / 8) / bytesPerGasUnit))
        modify fun st => st.consumeGas (gasTotal - gasConsumed)
        gasConsumed := gasTotal
        acc := acc.appendBits bits

      -- C++: `stack.pop_many(cnt);` before `finish()`.
      modify fun st => { st with stack := st.stack.take (st.stack.size - cnt) }

      let inputBytes ←
        match acc.finish with
        | .ok bs => pure bs
        | .error e => throw e

      let digest : ByteArray :=
        match hashId with
        | 0 => hashSha256 (ByteArray.mk inputBytes)
        | 1 => hashSha512 (ByteArray.mk inputBytes)
        | 2 => hashBlake2b (ByteArray.mk inputBytes)
        | 3 => hashKeccak256 (ByteArray.mk inputBytes)
        | 4 => hashKeccak512 (ByteArray.mk inputBytes)
        | _ => ByteArray.mk #[]

      if digest.size != digestSize then
        throw .unknown

      if append then
        let b ← VM.popBuilder
        if !b.canExtendBy (digest.size * 8) then
          throw .cellOv
        let mut outBits : BitString := #[]
        for j in [0:digest.size] do
          outBits := outBits ++ natToBits (digest.get! j).toNat 8
        VM.push (.builder (b.storeBits outBits))
      else
        if digest.size ≤ 32 then
          let n := byteArrayToNatBE digest
          VM.pushIntQuiet (.num (Int.ofNat n)) false
        else
          let mut res : Array Value := #[]
          let mut off : Nat := 0
          while off < digest.size do
            let len := Nat.min 32 (digest.size - off)
            let chunk := digest.extract off (off + len)
            let n := byteArrayToNatBE chunk
            res := res.push (.int (.num (Int.ofNat n)))
            off := off + 32
          VM.push (.tuple res)
  | .hashCU =>
      let c ← VM.popCell
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | .hashSU =>
      let s ← VM.popSlice
      -- C++ `HASHSU` builds a temporary cell from the slice and hashes it; `CellBuilder::finalize()`
      -- charges `cell_create_gas_price`.
      modify fun st => st.consumeGas cellCreateGasPrice
      let c := s.toCellRemaining
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | .chkSignU =>
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
      let ok := ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | .chkSignS =>
      let key ← VM.popInt
      let sigSlice ← VM.popSlice
      let dataSlice ← VM.popSlice
      if dataSlice.bitsRemaining % 8 ≠ 0 then
        throw .cellUnd
      let dataLen : Nat := dataSlice.bitsRemaining / 8
      if dataLen > 128 then
        throw .rangeChk

      let msgBytes ←
        match dataSlice.prefetchBytesCellUnd dataLen with
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
      let ok := ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | _ => next

end TvmLean
