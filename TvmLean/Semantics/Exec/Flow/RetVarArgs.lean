import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowRetVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .retVarArgs =>
      -- Mirrors C++ `exec_ret_varargs`: pop `retvals ∈ [-1..254]` and `RET` with `passArgs=retvals`.
      -- C++ uses `pop_smallint_range(254, -1)`, which maps NaN/non-smallint to `range_chk`.
      let retvals ← VM.popInt
      match retvals with
      | .nan =>
          throw .rangeChk
      | .num n =>
          if decide (n < -1 ∨ n > 254) then
            throw .rangeChk
          VM.ret n
  | _ => next

end TvmLean
