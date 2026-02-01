import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMulDivMod (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .mulDivMod d roundMode addMode quiet =>
      -- Matches C++ `exec_muldivmod` (arithops.cpp).
      let z ← VM.popInt
      let w ←
        if addMode then
          VM.popInt
        else
          pure (.num 0)
      let y ← VM.popInt
      let x ← VM.popInt
      match x, w, y, z with
      | .num xn, .num wn, .num yn, .num zn =>
          if zn = 0 then
            if d == 3 then
              VM.pushIntQuiet .nan quiet
              VM.pushIntQuiet .nan quiet
            else
              VM.pushIntQuiet .nan quiet
          else if roundMode != -1 && roundMode != 0 && roundMode != 1 then
            throw .invOpcode
          else
            let tmp : Int := xn * yn + wn
            let (q, r) := divModRound tmp zn roundMode
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
      | _, _, _, _ =>
          if d == 3 then
            VM.pushIntQuiet .nan quiet
            VM.pushIntQuiet .nan quiet
          else
            VM.pushIntQuiet .nan quiet
  | _ => next

end TvmLean
