import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvSetGasLimit (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .setGasLimit =>
      let n ← VM.popIntFinite
      let gas63 : Int := Int.ofNat (1 <<< (63 : Nat))
      let newLimit : Int :=
        if n > 0 then
          if n < gas63 then n else GasLimits.infty
      else
        0
      let st ← get
      set { st with gas := st.gas.changeLimit newLimit }
  | _ => next

end TvmLean
