import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMulShrModConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .mulShrModConst d roundMode z =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .num a, .num b =>
          let tmp : Int := a * b
          match d with
          | 1 =>
              let q := rshiftPow2Round tmp z roundMode
              VM.pushIntQuiet (.num q) false
          | 2 =>
              let r := modPow2Round tmp z roundMode
              VM.pushIntQuiet (.num r) false
          | 3 =>
              let q := rshiftPow2Round tmp z roundMode
              let r := modPow2Round tmp z roundMode
              VM.pushIntQuiet (.num q) false
              VM.pushIntQuiet (.num r) false
          | _ =>
              throw .invOpcode
      | _, _ =>
          -- NaN propagation for MVP.
          if d == 3 then
            VM.pushIntQuiet .nan false
            VM.pushIntQuiet .nan false
          else
            VM.pushIntQuiet .nan false
  | _ => next

end TvmLean
