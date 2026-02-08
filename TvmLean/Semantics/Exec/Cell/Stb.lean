import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStb (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stb rev quiet =>
      -- Matches C++ `exec_store_builder(_rev)` (cellops.cpp).
      if rev then
        -- Stack: ... builder cb2 -- ...  (cb2 on top)
        let cb2 ← VM.popBuilder
        let b ← VM.popBuilder
        if b.canExtendBy cb2.bits.size cb2.refs.size then
          let b' : Builder := { bits := b.bits ++ cb2.bits, refs := b.refs ++ cb2.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.builder cb2)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... cb2 builder -- ...  (builder on top)
        let b ← VM.popBuilder
        let cb2 ← VM.popBuilder
        if b.canExtendBy cb2.bits.size cb2.refs.size then
          let b' : Builder := { bits := b.bits ++ cb2.bits, refs := b.refs ++ cb2.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder cb2)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | _ => next

end TvmLean
