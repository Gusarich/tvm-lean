import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictGetMinMax (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictGetMinMax args5 =>
      -- Matches C++ `exec_dict_getmin` (dictops.cpp).
      let byRef : Bool := (args5 &&& 1) = 1
      let unsigned : Bool := (args5 &&& 2) = 2
      let intKey : Bool := (args5 &&& 4) = 4
      let fetchMax : Bool := (args5 &&& 8) = 8
      let remove : Bool := (args5 &&& 16) = 16
      let invertFirst : Bool := !unsigned
      let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
      let n ← VM.popNatUpTo maxN
      let dictCell? ← VM.popMaybeCell
      match dictCell? with
      | some c => modify fun st => st.registerCellLoad c
      | none => pure ()
      match dictMinMaxWithCells dictCell? n fetchMax invertFirst with
      | .error e => throw e
      | .ok (none, loaded) =>
          let loaded :=
            match dictCell? with
            | none => loaded
            | some root => loaded.filter (fun c => c != root)
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if remove then
            match dictCell? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
          VM.pushSmallInt 0
      | .ok (some (val0, keyBits), loaded0) =>
          let loaded0 :=
            match dictCell? with
            | none => loaded0
            | some root => loaded0.filter (fun c => c != root)
          for c in loaded0 do
            modify fun st => st.registerCellLoad c
          let mut val := val0
          let mut dictOut? : Option Cell := dictCell?
          let mut created : Nat := 0
          let mut loaded1 : Array Cell := #[]
          if remove then
            match dictDeleteWithCells dictCell? keyBits with
            | .error e => throw e
            | .ok (oldVal?, newRoot?, created1, loadedDel) =>
                match oldVal? with
                | none => throw .dictErr
                | some oldVal =>
                    val := oldVal
                    dictOut? := newRoot?
                    created := created1
                    loaded1 := loadedDel
          for c in loaded1 do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)

          if remove then
            match dictOut? with
            | none => VM.push .null
            | some c => VM.push (.cell c)

          if byRef then
            if val.bitsRemaining == 0 && val.refsRemaining == 1 then
              let c := val.cell.refs[val.refPos]!
              VM.push (.cell c)
            else
              throw .dictErr
          else
            VM.push (.slice val)

          if intKey then
            let keyOut : Int :=
              if invertFirst then
                bitsToIntSignedTwos keyBits
              else
                Int.ofNat (bitsToNat keyBits)
            VM.pushIntQuiet (.num keyOut) false
          else
            modify fun st => st.consumeGas cellCreateGasPrice
            let keyCell : Cell := Cell.mkOrdinary keyBits #[]
            VM.push (.slice (Slice.ofCell keyCell))

          VM.pushSmallInt (-1)
  | _ => next

end TvmLean
