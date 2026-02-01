import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithQpow2 (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .qpow2 =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan true
      | .num n =>
          if n < 0 then
            throw .rangeChk
          let exp := n.toNat
          if exp > 255 then
            throw .rangeChk
          VM.pushIntQuiet (.num (intPow2 exp)) true
  | _ => next

end TvmLean
