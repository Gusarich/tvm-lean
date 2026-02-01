import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpTpop (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .tpop =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 ∨ items.size < 1 then
            throw .typeChk
          let out := items.pop
          let x := items[items.size - 1]!
          modify fun st => st.consumeTupleGas out.size
          VM.push (.tuple out)
          VM.push x
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
