import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowSetcp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setcp cp =>
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        -- TON TVM currently supports only codepage 0 (cp0).
        throw .invOpcode
  | .setcpX =>
      let v ← VM.popInt
      let cp ←
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if decide (-0x8000 ≤ n ∧ n ≤ 0x7fff) then
              pure n
            else
              throw .rangeChk
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        -- TON TVM currently supports only codepage 0 (cp0).
        throw .invOpcode
  | _ => next

end TvmLean
