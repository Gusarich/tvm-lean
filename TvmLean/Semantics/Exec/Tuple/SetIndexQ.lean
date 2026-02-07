import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execTupleOpSetIndexQ (op : TupleInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .setIndexQ idx =>
      let x ← VM.pop
      let v ← VM.pop
      if idx ≥ 255 then
        throw .rangeChk
      let (tupOpt, tpay) : Option (Array Value) × Nat :=
        match v with
        | .null =>
            if x == .null then
              (none, 0)
            else
              let newT := (Array.replicate (idx + 1) Value.null).set! idx x
              (some newT, idx + 1)
        | .tuple items =>
            if items.size > 255 then
              (some items, 0) -- unreachable; handled below
            else if items.size ≤ idx then
              if x == .null then
                (some items, 0)
              else
                let out := (items ++ Array.replicate (idx + 1 - items.size) Value.null).set! idx x
                (some out, idx + 1)
            else
              let out := items.set! idx x
              (some out, items.size)
        | _ =>
            (none, 0) -- unreachable; handled below
      match v with
      | .tuple items =>
          if items.size > 255 then
            throw .typeChk
      | .null => pure ()
      | _ => throw .typeChk
      if tpay > 0 then
        modify fun st => st.consumeTupleGas tpay
      match tupOpt with
      | none =>
          VM.push .null
      | some items =>
          VM.push (.tuple items)
  | _ => next

end TvmLean
