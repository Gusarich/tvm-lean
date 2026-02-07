import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoHashExt (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp (.hashExt hashId0 append rev) =>
      -- Mirrors C++ `exec_hash_ext` (tonops.cpp).
      -- Args: hash_id8 + rev(bit8) + append(bit9). If hash_id8 = 255, read hash_id from stack.
      -- Stack (append=false):  ... x[cnt-1] ... x[0] cnt  -- ... hash
      -- Stack (append=true):   ... builder x[cnt-1] ... x[0] cnt  -- ... builder'
      let mut hashId : Nat := hashId0
      if hashId = 255 then
        -- C++ (modern TVM): `check_underflow(2); pop_smallint_range(254)`.
        VM.checkUnderflow 2
        hashId := (← VM.popNatUpTo 254)

      -- C++: `cnt = pop_smallint_range(stack.depth() - 1 - append)`
      let stBeforeCnt ← get
      let depth : Nat := stBeforeCnt.stack.size
      let maxCntInt : Int := Int.ofNat depth - 1 - (if append then 1 else 0)
      let cntVal ← VM.popInt
      let cnt : Nat ←
        match cntVal with
        | .nan => throw .rangeChk
        | .num n =>
            if decide (n < 0 ∨ n > maxCntInt) then
              throw .rangeChk
            else
              pure n.toNat

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
        | 0 => host.hashSha256 (ByteArray.mk inputBytes)
        | 1 => host.hashSha512 (ByteArray.mk inputBytes)
        | 2 => host.hashBlake2b (ByteArray.mk inputBytes)
        | 3 => host.hashKeccak256 (ByteArray.mk inputBytes)
        | 4 => host.hashKeccak512 (ByteArray.mk inputBytes)
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
  | _ => next

end TvmLean
