import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdEq (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdEq =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      -- Matches C++ `CellSlice::lex_cmp` equality: compare remaining bits and refs.
      let c1 := s1.toCellRemaining
      let c2 := s2.toCellRemaining
      VM.pushSmallInt (if c1 == c2 then -1 else 0)
  | _ => next

end TvmLean
