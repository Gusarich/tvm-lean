import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStSame (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stSame =>
      VM.checkUnderflow 3
      let vNat ← VM.popNatUpTo 1
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits (vNat == 1))))
      else
        throw .cellOv
  | _ => next

end TvmLean
