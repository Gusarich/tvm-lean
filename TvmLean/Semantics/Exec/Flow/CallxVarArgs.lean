import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def popCallxVarArgBounded : VM Int := do
  -- Mirrors C++ `Stack::pop_smallint_range(254, -1)` used by `exec_callx_varargs`:
  -- non-int -> `type_chk`, NaN/non-int64 sentinel -> `range_chk`, and bounds violations -> `range_chk`.
  let v ← VM.popInt
  match v with
  | .nan =>
      throw .rangeChk
  | .num n =>
      if decide (n < -1 ∨ n > 254) then
        throw .rangeChk
      else
        pure n

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxVarArgs =>
      -- Mirrors C++ `exec_callx_varargs`: pop `retvals`, `params` (both in [-1..254]) and call the continuation.
      VM.checkUnderflow 3
      let retVals ← popCallxVarArgBounded
      let params ← popCallxVarArgBounded
      let cont ← VM.popCont
      VM.call cont params retVals
  | _ => next

end TvmLean
