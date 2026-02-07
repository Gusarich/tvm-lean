import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpTpush (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .tpush =>
      let x ← VM.pop
      let t ← VM.pop
      match t with
      | .tuple items =>
          if items.size > 254 then
            throw .rangeChk
          let out := items.push x
          VM.push (.tuple out)
          modify fun st => st.consumeTupleGas out.size
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
