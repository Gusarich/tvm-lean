import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetGasFeeSimple (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getGasFeeSimple =>
      -- Matches C++ `exec_get_gas_fee_simple` (tonops.cpp).
      -- Stack: ... gas_used is_masterchain -- ... gas_fee_simple
      let isMasterchain ← VM.popBool
      let max63 : Nat := (1 <<< 63) - 1
      let gasUsed ← VM.popNatUpTo max63
      let (gasPrice, _, _) ← VM.getGasPrices isMasterchain
      let fee : Int := ceilDivPow2 (Int.ofNat gasPrice * Int.ofNat gasUsed) 16
      VM.pushIntQuiet (.num fee) false
  | _ => next

end TvmLean
