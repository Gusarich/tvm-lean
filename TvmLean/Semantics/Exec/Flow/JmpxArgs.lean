import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpxArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpxArgs params =>
      -- Mirrors C++ `exec_jmpx_args`: pop continuation, then delegate
      -- all pass-args checks/stack shaping to `VmState::jump(..., pass_args)`.
      let cont ← VM.popCont
      VM.jump cont (Int.ofNat params)
  | _ => next

end TvmLean
