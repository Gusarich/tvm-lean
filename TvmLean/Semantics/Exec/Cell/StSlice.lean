import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStSlice (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stSlice rev quiet =>
      VM.checkUnderflow 2
      let (b, s) ←
        if rev then
          -- Stack: ... builder slice -- ...
          let s ← VM.popSlice
          let b ← VM.popBuilder
          pure (b, s)
        else
          -- Stack: ... slice builder -- ...
          let b ← VM.popBuilder
          let s ← VM.popSlice
          pure (b, s)
      let c := s.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
        VM.push (.builder b')
        if quiet then
          VM.pushSmallInt 0
      else
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.slice s)
          else
            VM.push (.slice s)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
  | _ => next

end TvmLean
