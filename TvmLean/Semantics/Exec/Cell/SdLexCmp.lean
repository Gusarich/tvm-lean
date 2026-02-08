import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdLexCmp (i : Instr) (next : VM Unit) : VM Unit := do
  let lexCmpBits (b1 b2 : BitString) : Int :=
    let len1 := b1.size
    let len2 := b2.size
    let len := min len1 len2
    let cmp? :=
      (List.range len).foldl
        (fun acc idx =>
          match acc with
          | some v => some v
          | none =>
              let bit1 := b1[idx]!
              let bit2 := b2[idx]!
              if bit1 == bit2 then none else some (if bit1 then 1 else -1))
        none
    match cmp? with
    | some v => v
    | none =>
        if len1 == len2 then 0 else if len1 < len2 then -1 else 1
  match i with
  | .sdLexCmp =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      -- Matches C++ `CellSlice::lex_cmp`: compare only remaining bits (ignore refs).
      let b1 := s1.readBits s1.bitsRemaining
      let b2 := s2.readBits s2.bitsRemaining
      VM.pushSmallInt (lexCmpBits b1 b2)
  | _ => next

end TvmLean
