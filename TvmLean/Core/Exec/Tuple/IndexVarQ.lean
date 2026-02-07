import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIndexVarQ (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .indexVarQ =>
      VM.checkUnderflow 2
      let idx ← VM.popNatUpTo 254
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
