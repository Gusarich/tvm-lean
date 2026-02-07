import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpMktuple (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .mktuple n =>
      let st ← get
      if n ≤ st.stack.size then
        let mut items : Array Value := #[]
        for _ in [0:n] do
          items := items.push (← VM.pop)
        VM.push (.tuple items.reverse)
        modify fun st => st.consumeTupleGas n
      else
        throw .stkUnd
  | _ => next

end TvmLean
