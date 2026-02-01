import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpSplit (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .split quiet =>
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if !s.haveBits bits || !s.haveRefs refs then
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let stop : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
        let prefixCell : Cell := Slice.prefixCell s stop
        let sPrefix : Slice := Slice.ofCell prefixCell
        let sRest : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
        VM.push (.slice sPrefix)
        VM.push (.slice sRest)
        if quiet then
          VM.pushSmallInt (-1)
  | _ => next

end TvmLean
