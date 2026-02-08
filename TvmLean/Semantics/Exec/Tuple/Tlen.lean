import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpTlen (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .tlen =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
          VM.pushSmallInt (Int.ofNat items.size)
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
