import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIndexQ (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .indexQ idx =>
      let v ← VM.pop
      match v with
      | .null =>
          VM.push .null
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
          if idx < items.size then
            VM.push (items[idx]!)
          else
            VM.push .null
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
