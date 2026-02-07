import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackPushInt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushInt n =>
      match n with
      | .nan => VM.push (.int .nan)
      | _ => VM.pushIntQuiet n false
  | _ => next

end TvmLean
