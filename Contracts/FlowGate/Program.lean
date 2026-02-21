import TvmLean.Proof.Program
import TvmLean.Native.Host.StubHost

namespace Contracts.FlowGate.Program

open TvmLean

def initialState : VmState :=
  { (VmState.initial Cell.empty GasLimits.infty) with
      stack := #[.int (.num 0), .cont (.quit 0)] }

def program : List Instr :=
  [ .if_ ]

def run : StepResult :=
  VmState.execProgram stubHost program initialState

end Contracts.FlowGate.Program
