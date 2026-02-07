import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictSkipdict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .skipdict =>
      let s ← VM.popSlice
      if !s.haveBits 1 then
        throw .cellUnd
      let present : Bool := (s.readBits 1)[0]!
      let needRefs : Nat := if present then 1 else 0
      if !s.haveRefs needRefs then
        throw .cellUnd
      VM.push (.slice { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs })
  | _ => next

end TvmLean
