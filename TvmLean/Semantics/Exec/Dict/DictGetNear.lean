import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def dropFirstRootLoad (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root =>
      Id.run do
        let mut skipped : Bool := false
        let mut out : Array Cell := #[]
        for c in loaded do
          if (!skipped) && c == root then
            skipped := true
          else
            out := out.push c
        out

set_option maxHeartbeats 1000000 in
def execInstrDictDictGetNear (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictGetNear args4 =>
      -- Matches C++ `exec_dict_getnear` (dictops.cpp).
      VM.checkUnderflow 3
      let allowEq : Bool := (args4 &&& 1) = 1
      let goUp : Bool := (args4 &&& 2) = 0
      let intKey : Bool := (args4 &&& 8) = 8
      let unsigned : Bool := intKey && ((args4 &&& 4) = 4)
      let sgnd : Bool := intKey && !unsigned
      let maxN : Nat := if intKey then (if unsigned then 256 else 257) else 1023
      let n ← VM.popNatUpTo maxN
      let dictCell? ← VM.popMaybeCell
      if intKey then
        let key ← VM.popIntFinite
        let (out?, loaded0) ←
          match dictKeyBits? key n unsigned with
          | some hintBits =>
              match dictCell? with
              | some c => VM.registerCellLoad c
              | none => pure ()
              match dictNearestWithCells dictCell? hintBits goUp allowEq sgnd with
              | .error e =>
                  let loaded := dropFirstRootLoad dictCell? (dictNearestVisitedCells dictCell? hintBits goUp allowEq sgnd)
                  for c in loaded do
                    VM.registerCellLoad c
                  throw e
              | .ok r => pure r
          | none =>
              let cond : Bool := (decide (0 ≤ key)) != goUp
              if cond then
                match dictCell? with
                | some c => VM.registerCellLoad c
                | none => pure ()
                match dictMinMaxWithCells dictCell? n (!goUp) sgnd with
                | .error e =>
                    let loaded := dropFirstRootLoad dictCell? (dictMinMaxVisitedCells dictCell? n (!goUp) sgnd)
                    for c in loaded do
                      VM.registerCellLoad c
                    throw e
                | .ok r => pure r
              else
                pure (none, #[])

        for c in dropFirstRootLoad dictCell? loaded0 do
          VM.registerCellLoad c

        match out? with
        | none =>
            VM.pushSmallInt 0
        | some (val, keyBits) =>
            VM.push (.slice val)
            let keyOut : Int :=
              if sgnd then
                bitsToIntSignedTwos keyBits
              else
                Int.ofNat (bitsToNat keyBits)
            VM.pushIntQuiet (.num keyOut) false
            VM.pushSmallInt (-1)
      else
        let keyHint ← VM.popSlice
        if !keyHint.haveBits n then
          throw .cellUnd
        let hintBits : BitString := keyHint.readBits n
        match dictCell? with
        | some c => VM.registerCellLoad c
        | none => pure ()
        match dictNearestWithCells dictCell? hintBits goUp allowEq false with
        | .error e =>
            let loaded := dropFirstRootLoad dictCell? (dictNearestVisitedCells dictCell? hintBits goUp allowEq false)
            for c in loaded do
              VM.registerCellLoad c
            throw e
        | .ok (none, loaded) =>
            for c in dropFirstRootLoad dictCell? loaded do
              VM.registerCellLoad c
            VM.pushSmallInt 0
        | .ok (some (val, keyBits), loaded) =>
            for c in dropFirstRootLoad dictCell? loaded do
              VM.registerCellLoad c
            VM.push (.slice val)
            modify fun st => st.consumeGas cellCreateGasPrice
            let keyCell : Cell := Cell.mkOrdinary keyBits #[]
            VM.push (.slice (Slice.ofCell keyCell))
            VM.pushSmallInt (-1)
  | _ => next

end TvmLean
