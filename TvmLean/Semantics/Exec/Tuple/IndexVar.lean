import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIndexVar (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .indexVar =>
      VM.checkUnderflow 2
      let idx ← VM.popNatUpTo 254
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
          if idx < items.size then
            VM.push (items[idx]!)
          else
            throw .rangeChk
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
