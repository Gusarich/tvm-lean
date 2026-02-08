import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetForwardFeeSimple (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getForwardFeeSimple =>
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
  | _ => next

end TvmLean
