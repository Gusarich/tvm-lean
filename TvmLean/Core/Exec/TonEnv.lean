import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnv (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .balance =>
      -- BALANCE is `GETPARAM 7` in the TON opcode table; it reads `c7[0]` as the "params" tuple.
      let st ← get
      if h : 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 7 < params.size then
              VM.push (params[7]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | .now =>
      -- NOW is `GETPARAM 3` in the TON opcode table; it reads `c7[0]` as the "params" tuple.
      let st ← get
      if h : 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
          if 3 < params.size then
            VM.push (params[3]!)
          else
            throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | .getParam idx =>
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if idx < params.size then
              VM.push (params[idx]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | .getPrecompiledGas =>
      -- Same semantics as `GETPARAM 16` in the TON opcode table.
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 16 < params.size then
              VM.push (params[16]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | .randu256 =>
      let y ← VM.generateRandu256
      VM.pushIntQuiet (.num y) false
  | .rand =>
      let x ← VM.popIntFinite
      let y ← VM.generateRandu256
      let z := floorDivPow2 (x * y) 256
      VM.pushIntQuiet (.num z) false
  | .setRand mix =>
      let x ← VM.popIntFinite
      if decide (x < 0 ∨ x ≥ intPow2 256) then
        throw .rangeChk
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            let newSeed : Int ←
              if mix then
                if 6 < params.size then
                  match params[6]! with
                  | .int (.num seed) =>
                      if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                        throw .rangeChk
                      let seedBytes := natToBytesBEFixed seed.toNat 32
                      let xBytes := natToBytesBEFixed x.toNat 32
                      let digest := sha256Digest (seedBytes ++ xBytes)
                      pure (Int.ofNat (bytesToNatBE digest))
                  | .int .nan => throw .rangeChk
                  | _ => throw .typeChk
                else
                  throw .rangeChk
              else
                pure x

            let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
            let outerSize := st.regs.c7.size
            let c7' := st.regs.c7.set! 0 (.tuple params')
            let mut st' := { st with regs := { st.regs with c7 := c7' } }
            if tpay > 0 then
              st' := st'.consumeTupleGas tpay
            st' := st'.consumeTupleGas outerSize
            set st'
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | .getGlobVar =>
      let idx ← VM.popNatUpTo 254
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | .getGlob idx =>
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | .setGlobVar =>
      let idx ← VM.popNatUpTo 254
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | .setGlob idx =>
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | .accept =>
      let st ← get
      -- C++: change gas limit to GasLimits::infty.
      let st' := { st with gas := st.gas.changeLimit GasLimits.infty }
      set st'
  | .setGasLimit =>
      let n ← VM.popIntFinite
      let gas63 : Int := Int.ofNat (1 <<< (63 : Nat))
      let newLimit : Int :=
        if n > 0 then
          if n < gas63 then n else GasLimits.infty
        else
          0
      let st ← get
      if newLimit < st.gas.gasConsumed then
        throw .outOfGas
      set { st with gas := st.gas.changeLimit newLimit }
  | .gasConsumed =>
      let st ← get
      VM.pushSmallInt st.gas.gasConsumed
  | .commit =>
      let st ← get
      if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
        set { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } }
      else
        throw .cellOv
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
  | .ldMsgAddr quiet =>
      let csr0 ← VM.popSlice
      match csr0.skipMessageAddr with
      | .ok csr1 =>
          let addrCell := Slice.prefixCell csr0 csr1
          VM.push (.slice (Slice.ofCell addrCell))
          VM.push (.slice csr1)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.push (.slice csr0)
            VM.pushSmallInt 0
          else
            throw e
  | .rewriteStdAddr quiet =>
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
  | .globalId =>
      -- Matches C++ `exec_get_global_id` (tonops.cpp) for global_version >= 6.
      let unpacked ← VM.getUnpackedConfigTuple
      match unpacked.get? 1 with
      | some (.slice cs) =>
          if !cs.haveBits 32 then
            throw .cellUnd
          let gid : Int := bitsToIntSignedTwos (cs.readBits 32)
          VM.pushSmallInt gid
      | some .null => throw .invOpcode
      | some _ => throw .typeChk
      | none => throw .typeChk
  | .getGasFee =>
      -- Matches C++ `exec_get_gas_fee` / `GasLimitsPrices::compute_gas_price` (tonops.cpp, mc-config.h).
      -- Stack: ... gas_used is_masterchain -- ... gas_fee
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let gasUsed ← VM.popNatUpTo max63
      let (gasPrice, flatGasLimit, flatGasPrice) ← VM.getGasPrices isMasterchain
      let fee : Int :=
        if gasUsed ≤ flatGasLimit then
          Int.ofNat flatGasPrice
        else
          let varPart : Int := Int.ofNat gasPrice * Int.ofNat (gasUsed - flatGasLimit);
          Int.ofNat flatGasPrice + ceilDivPow2 varPart 16
      VM.pushIntQuiet (.num fee) false
  | .getStorageFee =>
      -- Matches C++ `exec_get_storage_fee` / `calculate_storage_fee` (tonops.cpp),
      -- using the already-selected `StoragePrices` entry from `UNPACKEDCONFIGTUPLE[0]`
      -- (computed outside TVM in `Config::get_unpacked_config_tuple`).
      -- Stack: ... cells bits delta is_masterchain -- ... storage_fee
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let delta ← VM.popNatUpTo max63
      let bits ← VM.popNatUpTo max63
      let cells ← VM.popNatUpTo max63
      let unpacked ← VM.getUnpackedConfigTuple
      match unpacked.get? 0 with
      | some .null =>
          VM.pushSmallInt 0
      | some (.slice pricesCs) =>
          -- StoragePrices#cc utime_since:uint32 bit_price:uint64 cell_price:uint64 mc_bit_price:uint64 mc_cell_price:uint64
          let (tag, s1) ← pricesCs.takeBitsAsNatCellUnd 8
          if tag != 0xcc then
            throw .cellUnd
          let (_, s2) ← s1.takeBitsAsNatCellUnd 32 -- utime_since
          let (bitPrice, s3) ← s2.takeBitsAsNatCellUnd 64
          let (cellPrice, s4) ← s3.takeBitsAsNatCellUnd 64
          let (mcBitPrice, s5) ← s4.takeBitsAsNatCellUnd 64
          let (mcCellPrice, _) ← s5.takeBitsAsNatCellUnd 64
          let bitP : Nat := if isMasterchain then mcBitPrice else bitPrice
          let cellP : Nat := if isMasterchain then mcCellPrice else cellPrice
          let total : Int :=
            (Int.ofNat cells * Int.ofNat cellP + Int.ofNat bits * Int.ofNat bitP) * Int.ofNat delta
          let fee : Int := ceilDivPow2 total 16
          VM.pushIntQuiet (.num fee) false
      | some _ => throw .typeChk
      | none => throw .typeChk
  | .getForwardFee =>
      -- Matches C++ `exec_get_forward_fee` (tonops.cpp).
      -- Stack: ... cells bits is_masterchain -- ... fwd_fee
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let bits ← VM.popNatUpTo max63
      let cells ← VM.popNatUpTo max63
      let (lumpPrice, bitPrice, cellPrice, _, _) ← VM.getMsgPrices isMasterchain
      let x : Int := bitPrice * Int.ofNat bits + cellPrice * Int.ofNat cells
      let res : Int := lumpPrice + ceilDivPow2 x 16
      VM.pushIntQuiet (.num res) false
  | .getOriginalFwdFee =>
      -- Matches C++ `exec_get_original_fwd_fee` (tonops.cpp).
      -- Stack: ... fwd_fee is_masterchain -- ... original_fwd_fee
      let isMasterchain ← VM.popBool
      let fwdFee ← VM.popIntFinite
      if fwdFee < 0 then
        throw .rangeChk
      let (_, _, _, _, firstFrac) ← VM.getMsgPrices isMasterchain
      if (1 <<< 16) ≤ firstFrac then
        throw .cellUnd
      let denom : Int := Int.ofNat ((1 <<< 16) - firstFrac)
      let res : Int := (fwdFee * intPow2 16) / denom
      VM.pushIntQuiet (.num res) false
  | .getGasFeeSimple =>
      -- Matches C++ `exec_get_gas_fee_simple` (tonops.cpp).
      -- Stack: ... gas_used is_masterchain -- ... gas_fee_simple
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let gasUsed ← VM.popNatUpTo max63
      let (gasPrice, _, _) ← VM.getGasPrices isMasterchain
      let fee : Int := ceilDivPow2 (Int.ofNat gasPrice * Int.ofNat gasUsed) 16
      VM.pushIntQuiet (.num fee) false
  | .getForwardFeeSimple =>
      -- Matches C++ `exec_get_forward_fee_simple` (tonops.cpp).
      -- Stack: ... cells bits is_masterchain -- ... fwd_fee_simple
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let bits ← VM.popNatUpTo max63
      let cells ← VM.popNatUpTo max63
      let (_, bitPrice, cellPrice, _, _) ← VM.getMsgPrices isMasterchain
      let x : Int := bitPrice * Int.ofNat bits + cellPrice * Int.ofNat cells
      let res : Int := ceilDivPow2 x 16
      VM.pushIntQuiet (.num res) false
  | .inMsgParam idx =>
      -- Matches C++ `exec_get_in_msg_param` / `exec_get_var_in_msg_param` (tonops.cpp).
      -- Stack: ... -- ... value
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if h17 : 17 < params.size then
              match params[17]! with
              | .tuple inMsgParams =>
                  if idx < inMsgParams.size then
                    VM.push (inMsgParams[idx]!)
                  else
                    throw .rangeChk
              | _ =>
                  throw .typeChk
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean
