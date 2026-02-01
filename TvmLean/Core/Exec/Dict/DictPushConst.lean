import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictPushConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictPushConst dict keyBits =>
      VM.push (.cell dict)
      VM.pushSmallInt (Int.ofNat keyBits)
  | _ => next

end TvmLean
