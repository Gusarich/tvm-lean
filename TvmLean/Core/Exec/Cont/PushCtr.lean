import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContPushCtr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushCtr idx =>
      let st ← get
      match st.getCtr idx with
      | .ok v => VM.push v
      | .error e => throw e
  | _ => next

end TvmLean
