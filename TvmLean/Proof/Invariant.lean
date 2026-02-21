import TvmLean.Semantics.Step.Proof

namespace TvmLean

abbrev Inv := VmState → Prop

abbrev InvStep (host : Host) (P : Inv) : Prop :=
  ∀ {st : VmState} {stNext : VmState},
    st.step host = .continue stNext → P st → P stNext

abbrev InvHalt (host : Host) (P : Inv) : Prop :=
  ∀ {st : VmState} {stNext : VmState} {exitCode : Int},
    st.step host = .halt exitCode stNext → P st → P stNext

theorem invStep_to_stepContinue (host : Host) (P : Inv) (hstep : InvStep host P) :
    ∀ {st : VmState} {stNext : VmState},
      StepContinue host st stNext → P st → P stNext := by
  intro st stNext hcont hP
  cases hcont with
  | intro hstepEq =>
      exact hstep hstepEq hP

theorem invHalt_to_stepHalt (host : Host) (P : Inv) (hhalt : InvHalt host P) :
    ∀ {st : VmState} {halted : Int × VmState},
      StepHalt host st halted → P st → P halted.2 := by
  intro st halted hhaltRel hP
  cases hhaltRel with
  | intro hstepEq =>
      exact hhalt hstepEq hP

theorem stepN_inv (host : Host) (P : Inv) (hstep : InvStep host P)
    {n : Nat} {st st' : VmState}
    (hsteps : StepN host n st st') (hP : P st) :
    P st' := by
  exact stepN_lift_invariant (host := host) (Inv := P)
    (hpres := invStep_to_stepContinue (host := host) (P := P) hstep) hsteps hP

theorem stepHaltN_inv (host : Host) (P : Inv) (hstep : InvStep host P) (hhalt : InvHalt host P)
    {n : Nat} {st st' : VmState} {exitCode : Int}
    (hsteps : StepHaltN host n st (exitCode, st')) (hP : P st) :
    P st' := by
  exact stepHaltN_lift_invariant (host := host) (Inv := P)
    (hcont := invStep_to_stepContinue (host := host) (P := P) hstep)
    (hhalt := invHalt_to_stepHalt (host := host) (P := P) hhalt) hsteps hP

theorem runK_inv (host : Host) (P : Inv) (hstep : InvStep host P)
    (fuel : Nat) (st st' : VmState)
    (hrun : VmState.runK host fuel st = .inr st') (hP : P st) :
    P st' := by
  exact runK_inr_lift_invariant (host := host) (Inv := P)
    (hpres := invStep_to_stepContinue (host := host) (P := P) hstep)
    (fuel := fuel) (st := st) (st' := st') hrun hP

theorem runK_halt_inv (host : Host) (P : Inv) (hstep : InvStep host P) (hhalt : InvHalt host P)
    (fuel : Nat) (st : VmState) (exitCode : Int) (st' : VmState)
    (hrun : VmState.runK host fuel st = .inl (exitCode, st')) (hP : P st) :
    P st' := by
  exact runK_inl_lift_invariant (host := host) (Inv := P)
    (hcont := invStep_to_stepContinue (host := host) (P := P) hstep)
    (hhalt := invHalt_to_stepHalt (host := host) (P := P) hhalt)
    (fuel := fuel) (st := st) (exitCode := exitCode) (st' := st') hrun hP

end TvmLean
