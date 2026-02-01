import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvSetRand (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setRand mix =>
      let x ← VM.popIntFinite
      if decide (x < 0 ∨ x ≥ intPow2 256) then
        throw .rangeChk
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            let newSeed : Int ←
              if mix then
                if 6 < params.size then
                  match params[6]! with
                  | .int (.num seed) =>
                      if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                        throw .rangeChk
                      let seedBytes := natToBytesBEFixed seed.toNat 32
                      let xBytes := natToBytesBEFixed x.toNat 32
                      let digest := sha256Digest (seedBytes ++ xBytes)
                      pure (Int.ofNat (bytesToNatBE digest))
                  | .int .nan => throw .rangeChk
                  | _ => throw .typeChk
                else
                  throw .rangeChk
              else
                pure x

            let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
            let outerSize := st.regs.c7.size
            let c7' := st.regs.c7.set! 0 (.tuple params')
            let mut st' := { st with regs := { st.regs with c7 := c7' } }
            if tpay > 0 then
              st' := st'.consumeTupleGas tpay
            st' := st'.consumeTupleGas outerSize
            set st'
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | _ => next

end TvmLean
