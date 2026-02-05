import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .arithExt op =>
      match op with
      | .qaddInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a + n)) true
      | .qmulInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a * n)) true
      | .fitsConst unsigned quiet bits =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan quiet
          | .num n =>
              let ok :=
                if unsigned then
                  intUnsignedFitsBits n bits
                else
                  intSignedFitsBits n bits
              if ok then
                VM.push (.int x)
              else if quiet then
                VM.push (.int .nan)
              else
                throw .intOv
      | .lshiftVar quiet =>
          let shift ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan quiet
          | .num n => VM.pushIntQuiet (.num (n * intPow2 shift)) quiet
      | .rshiftVar quiet =>
          let shift ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan quiet
          | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) quiet
      | .shrMod mulMode addMode d roundMode quiet zOpt =>
          let z ←
            match zOpt with
            | some z => pure z
            | none => VM.popNatUpTo 1023
          let w ← if addMode then VM.popInt else pure (.num 0)
          let y ← if mulMode then VM.popInt else pure (.num 1)
          let x ← VM.popInt
          match x, y, w with
          | .num xn, .num yn, .num wn =>
              if roundMode != -1 && roundMode != 0 && roundMode != 1 then
                throw .rangeChk
              let tmp0 : Int := if mulMode then xn * yn else xn
              let tmp : Int := if addMode then tmp0 + wn else tmp0
              match d with
              | 1 =>
                  let q := rshiftPow2Round tmp z roundMode
                  VM.pushIntQuiet (.num q) quiet
              | 2 =>
                  let r := modPow2Round tmp z roundMode
                  VM.pushIntQuiet (.num r) quiet
              | 3 =>
                  let q := rshiftPow2Round tmp z roundMode
                  let r := modPow2Round tmp z roundMode
                  VM.pushIntQuiet (.num q) quiet
                  VM.pushIntQuiet (.num r) quiet
              | _ =>
                  throw .rangeChk
          | _, _, _ =>
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
      | .shlDivMod d roundMode addMode quiet zOpt =>
          -- Stack order follows TVM `exec_shldivmod`: divisor is on top, shift amount just below it
          -- (unless `zOpt` is provided), then optional addend `w`, then `x`.
          let y ← VM.popInt
          let z ←
            match zOpt with
            | some z => pure z
            | none => VM.popNatUpTo 1023
          let w ← if addMode then VM.popInt else pure (.num 0)
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
                throw .rangeChk
              else
                let tmp : Int := xn * intPow2 z + wn
                let (q, r) := divModRound tmp yn roundMode
                match d with
                | 1 =>
                    VM.pushIntQuiet (.num q) quiet
                | 2 =>
                    VM.pushIntQuiet (.num r) quiet
                | 3 =>
                    VM.pushIntQuiet (.num q) quiet
                    VM.pushIntQuiet (.num r) quiet
                | _ =>
                    throw .rangeChk
          | _, _, _ =>
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
  | _ => next

end TvmLean
