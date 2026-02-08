import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpExplodeVar (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .explodeVar =>
      VM.checkUnderflow 2
      let maxLen ← VM.popNatUpTo 255
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size > maxLen then
            throw .typeChk
          if items.size > 255 then
            throw .typeChk
          let l : Nat := items.size
          for i in [0:l] do
            VM.push (items[i]!)
          modify fun st => st.consumeTupleGas l
          VM.pushSmallInt (Int.ofNat l)
      | _ =>
          throw .typeChk
  | _ => next

end TvmLean
