import TvmLean.Semantics.Step.Step

namespace TvmLean

def VmState.tryCommit (st : VmState) : Bool × VmState :=
  -- C++ also checks `level == 0`; our MVP has only ordinary cells (level 0).
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def VmState.commitResult (exitCode : Int) (st : VmState) : StepResult :=
  let (ok, st') := st.tryCommit
  if ok then
    .halt exitCode st'
  else
    -- C++: clear stack, push 0, return ~cell_ov on commit failure.
    let stFail := { st' with stack := #[.int (.num 0)] }
    .halt (~~~ Excno.cellOv.toInt) stFail

def VmState.finalizeHalt (exitCode : Int) (st : VmState) : StepResult :=
  if exitCode = -1 ∨ exitCode = -2 then
    st.commitResult exitCode
  else
    .halt exitCode st

def VmState.finalizeRunResult (res : StepResult) : StepResult :=
  match res with
  | .continue st' =>
      -- Defensive fallback: `runRaw` never returns `continue`, but keep this total.
      .halt (Excno.fatal.toInt) st'
  | .halt exitCode st' =>
      VmState.finalizeHalt exitCode st'

abbrev RunKResult := Sum (Int × VmState) VmState

def VmState.runK (host : Host) (fuel : Nat) (st : VmState) : RunKResult :=
  match fuel with
  | 0 => .inr st
  | fuel + 1 =>
      match st.step host with
      | .continue st' => VmState.runK host fuel st'
      | .halt exitCode st' => .inl (exitCode, st')

def VmState.runRaw (host : Host) (fuel : Nat) (st : VmState) : StepResult :=
  match VmState.runK host fuel st with
  | .inl (exitCode, st') => .halt exitCode st'
  | .inr st' => .halt (Excno.fatal.toInt) st'

def VmState.run (host : Host) (fuel : Nat) (st : VmState) : StepResult :=
  VmState.finalizeRunResult (VmState.runRaw host fuel st)

theorem runRaw_zero (host : Host) (st : VmState) :
    VmState.runRaw host 0 st = .halt (Excno.fatal.toInt) st := by
  simp [VmState.runRaw, VmState.runK]

theorem runRaw_succ (host : Host) (fuel : Nat) (st : VmState) :
    VmState.runRaw host (fuel + 1) st =
      match st.step host with
      | .continue st' => VmState.runRaw host fuel st'
      | .halt exitCode st' => .halt exitCode st' := by
  cases hstep : st.step host <;> simp [VmState.runRaw, VmState.runK, hstep]

theorem runK_zero (host : Host) (st : VmState) :
    VmState.runK host 0 st = .inr st := by
  rfl

theorem runK_succ (host : Host) (fuel : Nat) (st : VmState) :
    VmState.runK host (fuel + 1) st =
      match st.step host with
      | .continue st' => VmState.runK host fuel st'
      | .halt exitCode st' => .inl (exitCode, st') := by
  rfl

theorem VmState.runK_add (host : Host) (m n : Nat) (st : VmState) :
    VmState.runK host (m + n) st =
      match VmState.runK host m st with
      | .inl halted => .inl halted
      | .inr st' => VmState.runK host n st' := by
  induction m generalizing st with
  | zero =>
      simp [VmState.runK]
  | succ m ih =>
      simp [Nat.succ_add, VmState.runK]
      cases st.step host <;> simp [ih]

theorem VmState.runK_succ_of_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hcont : VmState.runK host fuel st = .inr st') :
    VmState.runK host (fuel + 1) st =
      match st'.step host with
      | .continue st'' => .inr st''
      | .halt exitCode st'' => .inl (exitCode, st'') := by
  simpa [hcont, VmState.runK] using
    (VmState.runK_add (host := host) (m := fuel) (n := 1) (st := st))

theorem VmState.runRaw_eq_of_runK_inl (host : Host) (fuel : Nat) (st : VmState)
    (exitCode : Int) (st' : VmState)
    (hhalt : VmState.runK host fuel st = .inl (exitCode, st')) :
    VmState.runRaw host fuel st = .halt exitCode st' := by
  simp [VmState.runRaw, hhalt]

theorem VmState.runRaw_eq_of_runK_inr (host : Host) (fuel : Nat) (st : VmState) (st' : VmState)
    (hcont : VmState.runK host fuel st = .inr st') :
    VmState.runRaw host fuel st = .halt (Excno.fatal.toInt) st' := by
  simp [VmState.runRaw, hcont]

theorem VmState.commitResult_ok (st : VmState) (exitCode : Int) (hok : st.tryCommit.fst = true) :
    VmState.commitResult exitCode st = .halt exitCode st.tryCommit.snd := by
  unfold VmState.commitResult
  simp [hok]

theorem VmState.finalizeHalt_commit_ok (st : VmState) (exitCode : Int)
    (hexit : exitCode = -1 ∨ exitCode = -2) (hok : st.tryCommit.fst = true) :
    VmState.finalizeHalt exitCode st = .halt exitCode st.tryCommit.snd := by
  unfold VmState.finalizeHalt
  simp [hexit, VmState.commitResult, hok]

theorem VmState.finalizeHalt_nonCommit (st : VmState) (exitCode : Int)
    (hexit : ¬ (exitCode = -1 ∨ exitCode = -2)) :
    VmState.finalizeHalt exitCode st = .halt exitCode st := by
  unfold VmState.finalizeHalt
  simp [hexit]

-- Backward-compatible one-step unfolding for proofs that reason about `run`.
theorem VmState.run_succ (host : Host) (fuel : Nat) (st : VmState) :
    VmState.run host (fuel + 1) st =
      match st.step host with
      | .continue st' => VmState.run host fuel st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st' := by
  unfold VmState.run
  rw [runRaw_succ]
  cases hstep : st.step host <;>
    simp [VmState.finalizeRunResult, VmState.finalizeHalt, VmState.commitResult]

theorem VmState.run_succ_finalized (host : Host) (fuel : Nat) (st : VmState) :
    VmState.run host (fuel + 1) st =
      match st.step host with
      | .continue st' => VmState.run host fuel st'
      | .halt exitCode st' => VmState.finalizeHalt exitCode st' := by
  simpa [VmState.finalizeHalt, VmState.commitResult] using
    (VmState.run_succ (host := host) (fuel := fuel) (st := st))

end TvmLean
