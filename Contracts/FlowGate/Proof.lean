import TvmLean.Proof
import Contracts.FlowGate.Program
import Contracts.FlowGate.Spec

namespace Contracts.FlowGate.Proof

open TvmLean
open Contracts.FlowGate.Program
open Contracts.FlowGate.Spec

theorem run_post : Post run := by
  unfold Post run program initialState
  rw [VmState.execProgram_single]
  rw [VmState.execProgramStep_unfold]
  native_decide

end Contracts.FlowGate.Proof
