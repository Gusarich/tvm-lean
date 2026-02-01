import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStSliceConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stSliceConst sConst =>
      let b ← VM.popBuilder
      let c := sConst.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
        VM.push (.builder b')
      else
        throw .cellOv
  | _ => next

end TvmLean
