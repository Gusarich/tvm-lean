import TvmLean.Proof.Invariant
import TvmLean.Proof.Program

namespace TvmLean

abbrev runK_add := VmState.runK_add

theorem runK_add_of_inr (host : Host) (m n : Nat) (st stMid : VmState)
    (hprefix : VmState.runK host m st = .inr stMid) :
    VmState.runK host (m + n) st = VmState.runK host n stMid := by
  simpa [hprefix] using (runK_add (host := host) (m := m) (n := n) (st := st))

theorem runK_add_inr (host : Host) (m n : Nat) (st stMid st' : VmState)
    (hprefix : VmState.runK host m st = .inr stMid)
    (hsuffix : VmState.runK host n stMid = .inr st') :
    VmState.runK host (m + n) st = .inr st' := by
  calc
    VmState.runK host (m + n) st = VmState.runK host n stMid := by
      exact runK_add_of_inr (host := host) (m := m) (n := n) (st := st) (stMid := stMid) hprefix
    _ = .inr st' := hsuffix

theorem runK_add_inl_left (host : Host) (m n : Nat) (st : VmState) (halted : Int × VmState)
    (hprefix : VmState.runK host m st = .inl halted) :
    VmState.runK host (m + n) st = .inl halted := by
  simpa [hprefix] using (runK_add (host := host) (m := m) (n := n) (st := st))

theorem runK_add_inl_right (host : Host) (m n : Nat) (st stMid : VmState)
    (halted : Int × VmState)
    (hprefix : VmState.runK host m st = .inr stMid)
    (hsuffix : VmState.runK host n stMid = .inl halted) :
    VmState.runK host (m + n) st = .inl halted := by
  calc
    VmState.runK host (m + n) st = VmState.runK host n stMid := by
      exact runK_add_of_inr (host := host) (m := m) (n := n) (st := st) (stMid := stMid) hprefix
    _ = .inl halted := hsuffix

theorem runK_add_inv (host : Host) (P : Inv) (hstep : InvStep host P)
    (m n : Nat) (st stMid st' : VmState)
    (hprefix : VmState.runK host m st = .inr stMid)
    (hsuffix : VmState.runK host n stMid = .inr st')
    (hP : P st) :
    P st' := by
  have hMid : P stMid :=
    runK_inv (host := host) (P := P) (hstep := hstep)
      (fuel := m) (st := st) (st' := stMid) hprefix hP
  exact runK_inv (host := host) (P := P) (hstep := hstep)
    (fuel := n) (st := stMid) (st' := st') hsuffix hMid

theorem runK_add_halt_inv (host : Host) (P : Inv)
    (hstep : InvStep host P) (hhalt : InvHalt host P)
    (m n : Nat) (st stMid st' : VmState) (exitCode : Int)
    (hprefix : VmState.runK host m st = .inr stMid)
    (hsuffix : VmState.runK host n stMid = .inl (exitCode, st'))
    (hP : P st) :
    P st' := by
  have hMid : P stMid :=
    runK_inv (host := host) (P := P) (hstep := hstep)
      (fuel := m) (st := st) (st' := stMid) hprefix hP
  exact runK_halt_inv (host := host) (P := P) (hstep := hstep) (hhalt := hhalt)
    (fuel := n) (st := stMid) (exitCode := exitCode) (st' := st') hsuffix hMid

theorem runK_split_inv (host : Host) (P : Inv) (hstep : InvStep host P)
    (m n : Nat) (st stMid st' : VmState)
    (hprefix : VmState.runK host m st = .inr stMid)
    (htotal : VmState.runK host (m + n) st = .inr st')
    (hP : P st) :
    P stMid ∧ P st' := by
  have hMid : P stMid :=
    runK_inv (host := host) (P := P) (hstep := hstep)
      (fuel := m) (st := st) (st' := stMid) hprefix hP
  have hsplit : VmState.runK host (m + n) st = VmState.runK host n stMid :=
    runK_add_of_inr (host := host) (m := m) (n := n) (st := st) (stMid := stMid) hprefix
  have hsuffix : VmState.runK host n stMid = .inr st' :=
    hsplit.symm.trans htotal
  exact ⟨hMid, runK_inv (host := host) (P := P) (hstep := hstep)
    (fuel := n) (st := stMid) (st' := st') hsuffix hMid⟩

theorem runK_split_halt_inv (host : Host) (P : Inv)
    (hstep : InvStep host P) (hhalt : InvHalt host P)
    (m n : Nat) (st stMid st' : VmState) (exitCode : Int)
    (hprefix : VmState.runK host m st = .inr stMid)
    (htotal : VmState.runK host (m + n) st = .inl (exitCode, st'))
    (hP : P st) :
    P stMid ∧ P st' := by
  have hMid : P stMid :=
    runK_inv (host := host) (P := P) (hstep := hstep)
      (fuel := m) (st := st) (st' := stMid) hprefix hP
  have hsplit : VmState.runK host (m + n) st = VmState.runK host n stMid :=
    runK_add_of_inr (host := host) (m := m) (n := n) (st := st) (stMid := stMid) hprefix
  have hsuffix : VmState.runK host n stMid = .inl (exitCode, st') :=
    hsplit.symm.trans htotal
  exact ⟨hMid, runK_halt_inv (host := host) (P := P) (hstep := hstep) (hhalt := hhalt)
    (fuel := n) (st := stMid) (exitCode := exitCode) (st' := st') hsuffix hMid⟩

def RunKResult.exitCode? : RunKResult → Option Int
  | .inl (exitCode, _) => some exitCode
  | .inr _ => none

def RunKResult.state : RunKResult → VmState
  | .inl (_, st) => st
  | .inr st => st

def VmState.runKExitCode? (host : Host) (fuel : Nat) (st : VmState) : Option Int :=
  (VmState.runK host fuel st).exitCode?

def VmState.runKState (host : Host) (fuel : Nat) (st : VmState) : VmState :=
  (VmState.runK host fuel st).state

theorem runKResult_exitCode?_inl (exitCode : Int) (st : VmState) :
    RunKResult.exitCode? (Sum.inl (exitCode, st) : RunKResult) = some exitCode := by
  rfl

theorem runKResult_exitCode?_inr (st : VmState) :
    RunKResult.exitCode? (Sum.inr st : RunKResult) = none := by
  rfl

theorem runKResult_state_inl (exitCode : Int) (st : VmState) :
    RunKResult.state (Sum.inl (exitCode, st) : RunKResult) = st := by
  rfl

theorem runKResult_state_inr (st : VmState) :
    RunKResult.state (Sum.inr st : RunKResult) = st := by
  rfl

theorem VmState.runKExitCode?_eq (host : Host) (fuel : Nat) (st : VmState) :
    VmState.runKExitCode? host fuel st = (VmState.runK host fuel st).exitCode? := by
  rfl

theorem VmState.runKState_eq (host : Host) (fuel : Nat) (st : VmState) :
    VmState.runKState host fuel st = (VmState.runK host fuel st).state := by
  rfl

theorem VmState.runK_succ_of_step_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hstep : st.step host = .continue st') :
    VmState.runK host (fuel + 1) st = VmState.runK host fuel st' := by
  simp [VmState.runK, hstep]

theorem VmState.runK_succ_of_step_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hstep : st.step host = .halt exitCode st') :
    VmState.runK host (fuel + 1) st = .inl (exitCode, st') := by
  simp [VmState.runK, hstep]

theorem VmState.runRaw_succ_of_step_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hstep : st.step host = .continue st') :
    VmState.runRaw host (fuel + 1) st = VmState.runRaw host fuel st' := by
  simp [runRaw_succ, hstep]

theorem VmState.runRaw_succ_of_step_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hstep : st.step host = .halt exitCode st') :
    VmState.runRaw host (fuel + 1) st = .halt exitCode st' := by
  simp [runRaw_succ, hstep]

theorem VmState.runRaw_state_eq_runKState (host : Host) (fuel : Nat) (st : VmState) :
    (VmState.runRaw host fuel st).state = VmState.runKState host fuel st := by
  unfold VmState.runRaw VmState.runKState RunKResult.state
  cases hrunK : VmState.runK host fuel st <;> simp [StepResult.state]

theorem VmState.runRaw_state_zero (host : Host) (st : VmState) :
    (VmState.runRaw host 0 st).state = st := by
  simp [VmState.runRaw, VmState.runK, StepResult.state]

theorem proof_api_smoke_step_continue_bridge (host : Host) (st st' : VmState)
    (hstep : st.step host = .continue st') :
    (VmState.runRaw host 1 st).state = VmState.runKState host 0 st' := by
  have hraw : VmState.runRaw host 1 st = VmState.runRaw host 0 st' := by
    simpa using
      VmState.runRaw_succ_of_step_continue (host := host) (fuel := 0) (st := st) (st' := st') hstep
  rw [hraw]
  exact VmState.runRaw_state_eq_runKState (host := host) (fuel := 0) (st := st')

end TvmLean
