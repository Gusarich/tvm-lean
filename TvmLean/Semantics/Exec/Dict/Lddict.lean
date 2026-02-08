import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictLddict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .lddict preload quiet =>
      let s ← VM.popSlice
      let ok : Bool :=
        if s.haveBits 1 then
          let present : Bool := (s.readBits 1)[0]!
          let needRefs : Nat := if present then 1 else 0
          s.haveRefs needRefs
        else
          false
      if !ok then
        if quiet then
          if !preload then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let present : Bool := (s.readBits 1)[0]!
        let needRefs : Nat := if present then 1 else 0
        if present then
          let c := s.cell.refs[s.refPos]!
          VM.push (.cell c)
        else
          VM.push .null
        if !preload then
          let s' : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs }
          VM.push (.slice s')
        if quiet then
          VM.pushSmallInt (-1)
  | _ => next

end TvmLean
