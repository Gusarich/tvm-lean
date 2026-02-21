import Contracts.FlowGate.Program

namespace Contracts.FlowGate.Spec

open TvmLean
open Contracts.FlowGate.Program

def Pre : Prop := True

def Post (res : StepResult) : Prop :=
  res.isContinue = true ∧ res.finalStack.size = 0

end Contracts.FlowGate.Spec
