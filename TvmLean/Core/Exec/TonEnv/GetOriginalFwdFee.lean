import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetOriginalFwdFee (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
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
  | _ => next

end TvmLean
