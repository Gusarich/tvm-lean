import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStSlice (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stSlice rev quiet =>
      if rev then
        -- Stack: ... builder slice -- ...
        let s ← VM.popSlice
        let b ← VM.popBuilder
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.slice s)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... slice builder -- ...
        let b ← VM.popBuilder
        let s ← VM.popSlice
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.slice s)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | _ => next

end TvmLean
