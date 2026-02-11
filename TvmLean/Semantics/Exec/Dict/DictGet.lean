import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictGet (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictGet intKey unsigned byRef =>
      VM.checkUnderflow 3
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits? : Option BitString ←
        if intKey then
          let idx ← VM.popIntFinite
          pure (dictKeyBits? idx n unsigned)
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (some (keySlice.readBits n))
          else
            throw .cellUnd
      match keyBits? with
      | none =>
          -- Dictionary index out of bounds: behave like "not found".
          VM.pushSmallInt 0
      | some keyBits =>
          match dictCell? with
          | some c => VM.registerCellLoad c
          | none => pure ()
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              let loadedAll := dictLookupVisitedCells dictCell? keyBits
              let loaded :=
                match dictCell? with
                | none => loadedAll
                | some root => loadedAll.filter (fun c => c != root)
              for c in loaded do
                VM.registerCellLoad c
              throw e
          | .ok (none, loaded) =>
              let loaded :=
                match dictCell? with
                | none => loaded
                | some root => loaded.filter (fun c => c != root)
              for c in loaded do
                VM.registerCellLoad c
              VM.pushSmallInt 0
          | .ok (some valueSlice, loaded) =>
              let loaded :=
                match dictCell? with
                | none => loaded
                | some root => loaded.filter (fun c => c != root)
              for c in loaded do
                VM.registerCellLoad c
              if byRef then
                if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                  let c := valueSlice.cell.refs[valueSlice.refPos]!
                  VM.push (.cell c)
                  VM.pushSmallInt (-1)
                else
                  throw .dictErr
              else
                VM.push (.slice valueSlice)
                VM.pushSmallInt (-1)
  | _ => next

end TvmLean
