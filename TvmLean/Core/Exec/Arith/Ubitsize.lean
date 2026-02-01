import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithUbitsize (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ubitsize quiet =>
      let x ← VM.popInt
      match x with
      | .nan =>
          if quiet then
            VM.pushIntQuiet .nan true
          else
            throw .rangeChk
      | .num n =>
          if n < 0 then
            throw .rangeChk
          else
            let width : Nat := natLenBits n.toNat
            VM.pushSmallInt (Int.ofNat width)
  | _ => next

end TvmLean
