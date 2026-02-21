import TvmLean.Proof
import TvmLean.Native.Host.StubHost
import Contracts.ToyCounter.Program
import Contracts.ToyCounter.Spec
import TvmLean.Proof.Examples.ToyCounterTrace

namespace Contracts.ToyCounter.Proof

open TvmLean
open Contracts.ToyCounter.Program
open Contracts.ToyCounter.Spec

def initState (x : Counter32) : VmState :=
  let st := VmState.initial Cell.empty GasLimits.infty
  { st with regs := { st.regs with c4 := initialC4 x } }

private theorem initState_pushCtr_budget (x : Counter32) :
    (GasBudget.ofInstr (.pushCtr 4)).sufficientFor (initState x) := by
  have hcost : instrGas (.pushCtr 4) 0 ≤ GasLimits.infty := by
    native_decide
  simpa [GasBudget.sufficientFor, GasBudget.ofInstr, initState, VmState.initial, GasLimits.ofLimits] using
    hcost

theorem initState_pushCtr_gas_checks (x : Counter32) :
    decide ((initState x).gas.gasRemaining < instrGas (.pushCtr 4) 0) = false ∧
      decide (((initState x).consumeGas (instrGas (.pushCtr 4) 0)).gas.gasRemaining < 0) = false := by
  have hsufficient : (GasBudget.ofInstr (.pushCtr 4)).sufficientFor (initState x) :=
    initState_pushCtr_budget x
  refine ⟨?_, ?_⟩
  · simpa [GasBudget.ofInstr] using
      (GasBudget.precheck_false (budget := GasBudget.ofInstr (.pushCtr 4)) (st := initState x) hsufficient)
  · simpa using
      (GasBudget.ofInstr_check_false (instr := .pushCtr 4) (st := initState x) hsufficient)

theorem initialC4_takeBits32_roundtrip (x : Counter32) :
    let s := Slice.ofCell (initialC4 x)
    s.takeBitsAsNatCellUnd 32 = .ok (bitsToNat (s.readBits 32), s.advanceBits 32) := by
  simpa [initialC4, encodeCounter] using
    (slice_storeBits32_takeBitsAsNat_roundtrip
      (bs := natToBits x.toNat 32)
      (hSize := by simp [natToBits]))

def runAsInstrProgram (x : Counter32) : StepResult :=
  VmState.execProgram stubHost program (initState x)

def runFromBytecode (x : Counter32) : Except Excno StepResult := do
  let code ← bytecode
  VmState.execDecodedCp0 stubHost decodeFuel code (initState x)

def runLegacy (x : Counter32) : Except Excno SpecState := do
  let st ← Proofs.ToyCounter.runToyCounter (Proofs.ToyCounter.init x)
  return { c4 := st.c4 }

def runLegacySpec (x : Counter32) : Except Excno SpecState := do
  let st ← Proofs.ToyCounter.runToyContract (Proofs.ToyCounter.init x)
  return { c4 := st.c4 }

theorem bytecode_roundtrip_check :
    assembleDecodeMatches decodeFuel program = true := by
  native_decide

theorem runFromBytecode_eq_execProgram (x : Counter32) (code : Cell)
    (hcode : bytecode = .ok code)
    (hdecode : decodeCp0AllFromCell decodeFuel code = .ok program) :
    runFromBytecode x = .ok (runAsInstrProgram x) := by
  unfold runFromBytecode runAsInstrProgram
  rw [hcode]
  exact VmState.execDecodedCp0_ok_of_decode stubHost decodeFuel code (initState x) program hdecode

theorem legacy_matches_spec (x : Counter32) :
    runLegacy x = runLegacySpec x := by
  have h := Proofs.ToyCounter.tvm_matches_spec x
  have hMap := congrArg (fun r => do
      let st ← r
      return ({ c4 := st.c4 } : SpecState)) h
  simpa [runLegacy, runLegacySpec] using hMap

end Contracts.ToyCounter.Proof
