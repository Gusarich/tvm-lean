import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSti (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sti bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STI`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          match intToBitsTwos n bits with
          | .ok bs => VM.push (.builder (b.storeBits bs))
          | .error e => throw e
  | _ => next

end TvmLean
