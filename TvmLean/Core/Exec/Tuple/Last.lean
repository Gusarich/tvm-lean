import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpLast (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .last =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 ∨ items.size < 1 then
            throw .typeChk
          VM.push (items[items.size - 1]!)
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
