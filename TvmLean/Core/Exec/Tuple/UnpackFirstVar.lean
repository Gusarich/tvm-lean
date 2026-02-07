import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpUnpackFirstVar (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .unpackFirstVar =>
      VM.checkUnderflow 2
      let n ← VM.popNatUpTo 255
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 ∨ items.size < n then
            throw .typeChk
          for i in [0:n] do
            VM.push (items[i]!)
          modify fun st => st.consumeTupleGas n
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
