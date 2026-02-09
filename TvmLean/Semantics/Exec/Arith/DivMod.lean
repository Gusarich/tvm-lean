import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithDivMod (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .divMod d roundMode addMode quiet =>
      let st ← get
      let need : Nat := if addMode then 3 else 2
      if st.stack.size < need then
        throw .stkUnd
      let y ← VM.popInt
      let w ←
        if addMode then
          VM.popInt
        else
          pure (.num 0)
      let x ← VM.popInt
      match x, w, y with
      | .num xn, .num wn, .num yn =>
          if yn = 0 then
            if d == 3 then
              VM.pushIntQuiet .nan quiet
              VM.pushIntQuiet .nan quiet
            else
              VM.pushIntQuiet .nan quiet
          else if roundMode != -1 && roundMode != 0 && roundMode != 1 then
            throw .invOpcode
          else
            let t : Int := xn + wn
            let (q, r) := divModRound t yn roundMode
            match d with
            | 1 =>
                VM.pushIntQuiet (.num q) quiet
            | 2 =>
                VM.pushIntQuiet (.num r) quiet
            | 3 =>
                VM.pushIntQuiet (.num q) quiet
                VM.pushIntQuiet (.num r) quiet
            | _ =>
                throw .invOpcode
      | _, _, _ =>
          if d == 3 then
            VM.pushIntQuiet .nan quiet
            VM.pushIntQuiet .nan quiet
          else
            VM.pushIntQuiet .nan quiet
  | _ => next

end TvmLean
