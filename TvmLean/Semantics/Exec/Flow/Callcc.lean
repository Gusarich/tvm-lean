import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def popCallccVarArgBounded : VM Int := do
  -- Mirrors C++ `Stack::pop_smallint_range(254, -1)` used by `exec_callcc_varargs`:
  -- non-int -> `type_chk`, NaN/non-int64 sentinel -> `range_chk`, bounds violations -> `range_chk`.
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
def execInstrFlowCallcc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callcc =>
      VM.checkUnderflow 1
      let cont ← VM.popCont
      let cc ← VM.extractCc 3
      VM.push (.cont cc)
      VM.jump cont
  | .callccArgs params retVals =>
      VM.checkUnderflow (params + 1)
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 (Int.ofNat params) retVals
      VM.push (.cont cc)
      VM.jump cont
  | .callccVarArgs =>
      VM.checkUnderflow 3
      let retVals ← popCallccVarArgBounded
      let params ← popCallccVarArgBounded
      let need : Nat := if decide (params ≥ 0) then params.toNat + 1 else 0
      VM.checkUnderflow need
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 params retVals
      VM.push (.cont cc)
      VM.jump cont
  | _ => next

end TvmLean
