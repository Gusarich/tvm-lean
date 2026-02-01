import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackTwoOver (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .twoOver =>
      let v1 ← VM.fetch 3
      VM.push v1
      let v2 ← VM.fetch 3
      VM.push v2
  | _ => next

end TvmLean
