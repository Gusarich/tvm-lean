import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithRshiftConst (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan =>
          -- Match C++ `exec_rshift_tinyint8`: invalid integers are shifted via
          -- `AnyIntView::rshift_any` instead of quiet-NaN funneling.
          let invalidCompat : IntVal :=
            if bits == 0 then
              .nan
            else if bits > (64 - 52) then
              .num (-1)
            else
              .num 0
          VM.pushIntQuiet invalidCompat quiet
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n bits)) quiet
  | _ => next

end TvmLean
