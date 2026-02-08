import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSubslice (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .subslice =>
      VM.checkUnderflow 5
      let r2 ← VM.popNatUpTo 4
      let l2 ← VM.popNatUpTo 1023
      let r1 ← VM.popNatUpTo 4
      let l1 ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if !s.haveBits l1 || !s.haveRefs r1 then
        throw .cellUnd
      let s1 : Slice := { s with bitPos := s.bitPos + l1, refPos := s.refPos + r1 }
      if !s1.haveBits l2 || !s1.haveRefs r2 then
        throw .cellUnd
      let stop : Slice := { s1 with bitPos := s1.bitPos + l2, refPos := s1.refPos + r2 }
      let newCell : Cell := Slice.prefixCell s1 stop
      VM.push (.slice (Slice.ofCell newCell))
  | _ => next

end TvmLean
