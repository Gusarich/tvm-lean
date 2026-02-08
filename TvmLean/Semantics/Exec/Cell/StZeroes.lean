import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStZeroes (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stZeroes =>
      VM.checkUnderflow 2
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits false)))
      else
        throw .cellOv
  | _ => next

end TvmLean
