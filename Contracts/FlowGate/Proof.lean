import TvmLean.Proof
import Contracts.FlowGate.Program
import Contracts.FlowGate.Spec

namespace Contracts.FlowGate.Proof

open TvmLean
open Contracts.FlowGate.Program
open Contracts.FlowGate.Spec

private theorem hgas_nonneg :
    ¬ (VmState.initial Cell.empty GasLimits.infty).gas.gasRemaining - instrGas .if_ 0 < 0 := by
  native_decide

theorem run_post : Post run := by
  unfold Post run program initialState
  rw [VmState.execProgram_single]
  rw [VmState.execProgramStep_unfold]
  have hrun :
      (execInstrSpecCore .if_).run
          ({ VmState.initial Cell.empty GasLimits.infty with
            stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas (instrGas .if_ 0)) =
        (.ok (),
          { ({ VmState.initial Cell.empty GasLimits.infty with
              stack := #[.int (.num 0), .cont (.quit 0)] }.consumeGas (instrGas .if_ 0)) with
            stack := #[] }) := by
    simpa using
      (instrSpec_if_false_run_consumed
        (st := VmState.initial Cell.empty GasLimits.infty) (g := instrGas .if_ 0))
  simp [hgas_nonneg, hrun]

end Contracts.FlowGate.Proof
