import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictGetExec (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictGetExec unsigned doCall pushZ =>
      VM.checkUnderflow 3
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let idx ← VM.popIntFinite
      match dictKeyBits? idx n unsigned with
      | none =>
          if pushZ then
            VM.push (.int (.num idx))
          else
            pure ()
      | some keyBits =>
          -- Match C++ `Dictionary` lookup path: entering dictionary traversal loads root once.
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
          | .ok (res?, loaded0) =>
              let loaded :=
                match dictCell? with
                | none => loaded0
                | some root => loaded0.filter (fun c => c != root)
              for c in loaded do
                VM.registerCellLoad c
              match res? with
              | none =>
                  if pushZ then
                    VM.push (.int (.num idx))
                  else
                    pure ()
              | some valueSlice =>
                  let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
                  modify fun st =>
                    if doCall then
                      st.callTo cont
                    else
                      st.jumpTo cont
  | _ => next

end TvmLean
