import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpUntuple (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .untuple n =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size = n then
            for i in [0:n] do
              VM.push (items[i]!)
            modify fun st => st.consumeTupleGas n
          else
            throw .typeChk
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
