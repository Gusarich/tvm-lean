import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIsTuple (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .isTuple =>
      let v ← VM.pop
      match v with
      | .tuple _ =>
          VM.pushSmallInt (-1)
      | _ =>
          VM.pushSmallInt 0
  | _ => next

end TvmLean
