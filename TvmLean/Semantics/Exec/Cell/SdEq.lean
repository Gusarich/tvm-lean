import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellSdEq (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sdEq =>
      -- Matches C++ `exec_bin_cs_cmp`: underflow is checked before type checks.
      VM.checkUnderflow 2
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      -- Matches C++ `CellSlice::lex_cmp`: compare only remaining bits (ignore refs).
      let b1 := s1.readBits s1.bitsRemaining
      let b2 := s2.readBits s2.bitsRemaining
      VM.pushSmallInt (if b1 == b2 then -1 else 0)
  | _ => next

end TvmLean
