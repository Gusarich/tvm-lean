import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTuple (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tupleOp op =>
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
      | .index idx =>
          let v ← VM.pop
          match v with
          | .tuple items =>
              if idx < items.size then
                VM.push (items[idx]!)
              else
                throw .rangeChk
          | _ =>
              throw .typeChk
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
      | .index3 i j k =>
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
                  let v2 := items1[j]!
                  match v2 with
                  | .tuple items2 =>
                      if items2.size > 255 then
                        throw .typeChk
                      if k ≥ items2.size then
                        throw .rangeChk
                      VM.push (items2[k]!)
                  | _ =>
                      throw .typeChk
              | _ =>
                  throw .typeChk
          | _ =>
              throw .typeChk
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
      | .unpackFirst n =>
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
      | .explode maxLen =>
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
      | .setIndex idx =>
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
      | .indexQ idx =>
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
      | .mktupleVar =>
          let n ← VM.popNatUpTo 255
          let st ← get
          if n ≤ st.stack.size then
            let mut items : Array Value := #[]
            for _ in [0:n] do
              items := items.push (← VM.pop)
            VM.push (.tuple items.reverse)
            modify fun st => st.consumeTupleGas n
          else
            throw .stkUnd
      | .indexVar =>
          let idx ← VM.popNatUpTo 254
          let v ← VM.pop
          match v with
          | .tuple items =>
              if items.size > 255 then
                throw .typeChk
              if idx < items.size then
                VM.push (items[idx]!)
              else
                throw .rangeChk
          | _ =>
              throw .typeChk
      | .untupleVar =>
          let n ← VM.popNatUpTo 255
          let v ← VM.pop
          match v with
          | .tuple items =>
              if items.size != n ∨ items.size > 255 then
                throw .typeChk
              for i in [0:n] do
                VM.push (items[i]!)
              modify fun st => st.consumeTupleGas n
          | _ =>
              throw .typeChk
      | .unpackFirstVar =>
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
      | .explodeVar =>
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
      | .setIndexVar =>
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
      | .indexVarQ =>
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
      | .setIndexVarQ =>
          let idx ← VM.popNatUpTo 254
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
      | .tlen =>
          let v ← VM.pop
          match v with
          | .tuple items =>
              if items.size > 255 then
                throw .typeChk
              VM.pushSmallInt (Int.ofNat items.size)
          | _ =>
              throw .typeChk
      | .qtlen =>
          let v ← VM.pop
          match v with
          | .tuple items =>
              if items.size > 255 then
                throw .typeChk
              VM.pushSmallInt (Int.ofNat items.size)
          | _ =>
              VM.pushSmallInt (-1)
      | .isTuple =>
          let v ← VM.pop
          match v with
          | .tuple _ =>
              VM.pushSmallInt (-1)
          | _ =>
              VM.pushSmallInt 0
      | .last =>
          let v ← VM.pop
          match v with
          | .tuple items =>
              if items.size > 255 ∨ items.size < 1 then
                throw .typeChk
              VM.push (items[items.size - 1]!)
          | _ =>
              throw .typeChk
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
