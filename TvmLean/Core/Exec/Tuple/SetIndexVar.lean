import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpSetIndexVar (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .setIndexVar =>
      VM.checkUnderflow 3
      let idx ← VM.popNatUpTo 254
      let x ← VM.pop
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
          if idx ≥ items.size then
            throw .rangeChk
          let out := items.set! idx x
          modify fun st => st.consumeTupleGas out.size
          VM.push (.tuple out)
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
