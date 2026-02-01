import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowPushRef (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushRef c =>
      -- Matches C++ `exec_push_ref` (cellops.cpp), mode 0: push cell without loading.
      VM.push (.cell c)
  | _ => next

end TvmLean
