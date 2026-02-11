import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retArgs n =>
      -- C++ `exec_ret_args` canonicalizes helper arg payload as `args & 15`.
      -- Decoded cp0 already yields [0..15], but this preserves helper parity
      -- for direct/constructed AST values as well.
      let params : Int := Int.ofNat (n &&& 0xf)
      VM.ret params
  | _ => next

end TvmLean
