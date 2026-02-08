import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpIndex2 (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .index2 i j =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
          if i ≥ items.size then
            throw .rangeChk
          let v1 := items[i]!
          match v1 with
          | .tuple items1 =>
              if items1.size > 255 then
                throw .typeChk
              if j ≥ items1.size then
                throw .rangeChk
              VM.push (items1[j]!)
          | _ =>
              throw .typeChk
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
