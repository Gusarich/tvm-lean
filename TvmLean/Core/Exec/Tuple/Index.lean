import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIndex (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .index idx =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if idx < items.size then
            VM.push (items[idx]!)
          else
            throw .rangeChk
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
