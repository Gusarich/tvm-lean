import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvConfigParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.configParam opt) =>
      -- Mirrors C++ `exec_get_config_param` (tonops.cpp).
      let idxVal ← VM.popInt
      VM.pushC7Param 9
      let dictRoot? ← VM.popMaybeCell
      let keyBits? : Option BitString :=
        match idxVal with
        | .nan => none
        | .num n =>
            if decide (n < 0 ∨ n ≥ intPow2 32) then
              none
            else
              some (natToBits n.toNat 32)
      match keyBits? with
      | none =>
          if opt then
            VM.push .null
          else
            VM.pushSmallInt 0
      | some keyBits =>
          match dictLookupWithCells dictRoot? keyBits with
          | .error e =>
              throw e
          | .ok (none, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              if opt then
                VM.push .null
              else
                VM.pushSmallInt 0
          | .ok (some valueSlice, loaded) =>
              for c in loaded do
                VM.registerCellLoad c
              if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                let c := valueSlice.cell.refs[valueSlice.refPos]!
                if opt then
                  VM.push (.cell c)
                else
                  VM.push (.cell c)
                  VM.pushSmallInt (-1)
              else
                throw .dictErr
  | _ => next

end TvmLean

