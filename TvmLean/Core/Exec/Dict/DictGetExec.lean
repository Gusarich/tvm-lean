import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictGetExec (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictGetExec unsigned doCall pushZ =>
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
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              throw e
          | .ok (res?, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
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
