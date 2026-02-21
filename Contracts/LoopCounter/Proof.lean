import Contracts.LoopCounter.Program
import Contracts.LoopCounter.Spec
import TvmLean.Proof.Invariant

namespace Contracts.LoopCounter.Proof

open Contracts.LoopCounter.Program
open Contracts.LoopCounter.Spec

theorem vm_runK_preserves_inv
    (host : TvmLean.Host) (P : TvmLean.Inv) (hstep : TvmLean.InvStep host P)
    (fuel : Nat) (st st' : TvmLean.VmState)
    (hrun : TvmLean.VmState.runK host fuel st = .inr st')
    (hP : P st) :
    P st' := by
  exact TvmLean.runK_inv (host := host) (P := P) (hstep := hstep)
    (fuel := fuel) (st := st) (st' := st') hrun hP

theorem runFromInit_sumInvariant (n : Nat) :
    SumInvariant n (Contracts.LoopCounter.Spec.runFromInit n) := by
  unfold SumInvariant Contracts.LoopCounter.Spec.runFromInit Contracts.LoopCounter.Spec.run Contracts.LoopCounter.Spec.init
  simpa [initState] using
    runCounter_preserves_sum (fuel := n) (st := initState n)

theorem runFromInit_post (n : Nat) :
    Post n (Contracts.LoopCounter.Spec.runFromInit n) := by
  refine ⟨?_, ?_⟩
  · simpa [Contracts.LoopCounter.Spec.runFromInit, Contracts.LoopCounter.Spec.run, Contracts.LoopCounter.Spec.init, initState] using
      runCounter_remaining_zero (fuel := n) (counter := 0)
  · have hsum : SumInvariant n (Contracts.LoopCounter.Spec.runFromInit n) :=
      runFromInit_sumInvariant n
    have hrem : (Contracts.LoopCounter.Spec.runFromInit n).remaining = 0 := by
      simpa [Contracts.LoopCounter.Spec.runFromInit, Contracts.LoopCounter.Spec.run, Contracts.LoopCounter.Spec.init, initState] using
        runCounter_remaining_zero (fuel := n) (counter := 0)
    unfold SumInvariant at hsum
    rw [hrem] at hsum
    simpa using hsum

end Contracts.LoopCounter.Proof
