import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStu (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stu bits =>
      if bits == 0 then
        throw .rangeChk
      VM.checkUnderflow 2
      -- Match C++ operand order for `STU`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if decide (n < 0 ∨ n ≥ intPow2 bits) then
            throw .rangeChk
          let bs := natToBits n.toNat bits
          VM.push (.builder (b.storeBits bs))
  | _ => next

end TvmLean
