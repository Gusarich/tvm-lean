import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetStorageFee (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getStorageFee =>
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
  | _ => next

end TvmLean
