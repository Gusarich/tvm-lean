import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowSetcp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setcp cp =>
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        throw .invOpcode
  | _ => next

end TvmLean
