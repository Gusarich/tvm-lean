import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetGasFee (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getGasFee =>
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
  | _ => next

end TvmLean
