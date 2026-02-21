import TvmLean.Semantics.Step.Run

namespace TvmLean

inductive StepContinue (host : Host) : VmState → VmState → Prop where
  | intro {st st' : VmState} (hstep : st.step host = .continue st') : StepContinue host st st'

inductive StepHalt (host : Host) : VmState → Int × VmState → Prop where
  | intro {st st' : VmState} {exitCode : Int}
      (hstep : st.step host = .halt exitCode st') : StepHalt host st (exitCode, st')

scoped notation:50 st " -[" host "]-> " st' => StepContinue host st st'
scoped notation:50 st " -[" host "]->halt " halted => StepHalt host st halted

inductive StepN (host : Host) : Nat → VmState → VmState → Prop where
  | zero (st : VmState) : StepN host 0 st st
  | succ {n : Nat} {st st' st'' : VmState} :
      StepContinue host st st' →
      StepN host n st' st'' →
      StepN host (n + 1) st st''

scoped notation:50 st " -[" host ", " n "]-> " st' => StepN host n st st'

inductive StepHaltN (host : Host) : Nat → VmState → Int × VmState → Prop where
  | base {st : VmState} {halted : Int × VmState} :
      StepHalt host st halted →
      StepHaltN host 1 st halted
  | succ {n : Nat} {st st' : VmState} {halted : Int × VmState} :
      StepContinue host st st' →
      StepHaltN host n st' halted →
      StepHaltN host (n + 1) st halted

scoped notation:50 st " -[" host ", " n "]->halt " halted => StepHaltN host n st halted

theorem runRaw_succ_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hstep : st.step host = .continue st') :
    VmState.runRaw host (fuel + 1) st = VmState.runRaw host fuel st' := by
  simp [runRaw_succ, hstep]

theorem runRaw_succ_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hstep : st.step host = .halt exitCode st') :
    VmState.runRaw host (fuel + 1) st = .halt exitCode st' := by
  simp [runRaw_succ, hstep]

theorem VmState.run_succ_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hstep : st.step host = .continue st') :
    VmState.run host (fuel + 1) st = VmState.run host fuel st' := by
  simp [VmState.run_succ_finalized, hstep]

theorem VmState.run_succ_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hstep : st.step host = .halt exitCode st') :
    VmState.run host (fuel + 1) st = VmState.finalizeHalt exitCode st' := by
  simp [VmState.run_succ_finalized, hstep]

theorem stepN_to_runK (host : Host) (n : Nat) (st st' : VmState)
    (hsteps : st -[host, n]-> st') :
    VmState.runK host n st = Sum.inr st' := by
  induction hsteps with
  | zero st =>
      simp [VmState.runK]
  | succ hcont _ ih =>
      cases hcont with
      | intro hstep =>
          simp [VmState.runK, hstep, ih]

theorem stepN_to_runRaw (host : Host) (n : Nat) (st st' : VmState)
    (hsteps : st -[host, n]-> st') :
    VmState.runRaw host n st = .halt (Excno.fatal.toInt) st' := by
  have hrunK : VmState.runK host n st = Sum.inr st' :=
    stepN_to_runK (host := host) (n := n) (st := st) (st' := st') hsteps
  simp [VmState.runRaw, hrunK]

theorem stepHaltN_to_runRaw (host : Host) (n : Nat) (st : VmState) (halted : Int × VmState)
    (hsteps : st -[host, n]->halt halted) :
    VmState.runRaw host n st = .halt halted.1 halted.2 := by
  induction hsteps with
  | base hhalt =>
      cases hhalt with
      | intro hstep =>
          simp [VmState.runRaw, VmState.runK, hstep]
  | succ hcont _ ih =>
      cases hcont with
      | intro hstep =>
          simp [runRaw_succ, hstep, ih]

theorem runK_inr_to_stepN (host : Host) (fuel : Nat) (st st' : VmState)
    (hcont : VmState.runK host fuel st = Sum.inr st') :
    st -[host, fuel]-> st' := by
  induction fuel generalizing st with
  | zero =>
      have hEq : st = st' := by simpa [VmState.runK] using hcont
      subst st'
      exact StepN.zero st
  | succ fuel ih =>
      cases hstep : st.step host
      · rename_i stNext
        have hnext : VmState.runK host fuel stNext = Sum.inr st' := by
          simpa [VmState.runK, hstep] using hcont
        exact StepN.succ (StepContinue.intro hstep) (ih (st := stNext) hnext)
      · simp [VmState.runK, hstep] at hcont

theorem runK_inl_to_stepHaltN (host : Host) (fuel : Nat) (st : VmState)
    (exitCode : Int) (st' : VmState)
    (hhalt : VmState.runK host fuel st = Sum.inl (exitCode, st')) :
    ∃ n, n ≤ fuel ∧ st -[host, n]->halt (exitCode, st') := by
  induction fuel generalizing st with
  | zero =>
      simp [VmState.runK] at hhalt
  | succ fuel ih =>
      cases hstep : st.step host
      · rename_i stNext
        have hnext : VmState.runK host fuel stNext = Sum.inl (exitCode, st') := by
          simpa [VmState.runK, hstep] using hhalt
        rcases ih (st := stNext) hnext with ⟨n, hn, hrel⟩
        refine ⟨n + 1, Nat.succ_le_succ hn, ?_⟩
        exact StepHaltN.succ (StepContinue.intro hstep) hrel
      · rename_i exitCode0 st0
        have hEq : (exitCode0, st0) = (exitCode, st') := by
          simpa [VmState.runK, hstep] using hhalt
        cases hEq
        refine ⟨1, Nat.succ_le_succ (Nat.zero_le fuel), ?_⟩
        exact StepHaltN.base (StepHalt.intro hstep)

theorem stepN_deterministic (host : Host) (n : Nat) (st st₁ st₂ : VmState)
    (h₁ : st -[host, n]-> st₁) (h₂ : st -[host, n]-> st₂) :
    st₁ = st₂ := by
  have hr1 : VmState.runK host n st = Sum.inr st₁ :=
    stepN_to_runK (host := host) (n := n) (st := st) (st' := st₁) h₁
  have hr2 : VmState.runK host n st = Sum.inr st₂ :=
    stepN_to_runK (host := host) (n := n) (st := st) (st' := st₂) h₂
  simpa [hr1] using hr2

theorem stepHaltN_deterministic (host : Host) (n : Nat) (st : VmState)
    (exitCode₁ exitCode₂ : Int) (st₁ st₂ : VmState)
    (h₁ : st -[host, n]->halt (exitCode₁, st₁))
    (h₂ : st -[host, n]->halt (exitCode₂, st₂)) :
    exitCode₁ = exitCode₂ ∧ st₁ = st₂ := by
  have hr1 : VmState.runRaw host n st = .halt exitCode₁ st₁ := by
    simpa using stepHaltN_to_runRaw (host := host) (n := n) (st := st) (halted := (exitCode₁, st₁)) h₁
  have hr2 : VmState.runRaw host n st = .halt exitCode₂ st₂ := by
    simpa using stepHaltN_to_runRaw (host := host) (n := n) (st := st) (halted := (exitCode₂, st₂)) h₂
  have : (.halt exitCode₁ st₁ : StepResult) = .halt exitCode₂ st₂ := by simpa [hr1] using hr2
  cases this
  exact ⟨rfl, rfl⟩

inductive RunScript (host : Host) : Nat → VmState → RunKResult → Prop where
  | done (st : VmState) : RunScript host 0 st (Sum.inr st)
  | next {fuel : Nat} {st st' : VmState} {res : RunKResult} :
      st.step host = .continue st' →
      RunScript host fuel st' res →
      RunScript host (fuel + 1) st res
  | halted {fuel : Nat} {st st' : VmState} {exitCode : Int} :
      st.step host = .halt exitCode st' →
      RunScript host (fuel + 1) st (Sum.inl (exitCode, st'))

theorem runK_of_script (host : Host) (fuel : Nat) (st : VmState) (res : RunKResult)
    (hscript : RunScript host fuel st res) :
    VmState.runK host fuel st = res := by
  induction hscript with
  | done st =>
      simp [VmState.runK]
  | next hstep _ ih =>
      simp [VmState.runK, hstep, ih]
  | halted hstep =>
      simp [VmState.runK, hstep]

theorem runRaw_of_script_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hscript : RunScript host fuel st (Sum.inl (exitCode, st'))) :
    VmState.runRaw host fuel st = .halt exitCode st' := by
  have hrunK : VmState.runK host fuel st = Sum.inl (exitCode, st') :=
    runK_of_script (host := host) (fuel := fuel) (st := st) (res := Sum.inl (exitCode, st')) hscript
  simp [VmState.runRaw, hrunK]

theorem runRaw_of_script_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hscript : RunScript host fuel st (Sum.inr st')) :
    VmState.runRaw host fuel st = .halt (Excno.fatal.toInt) st' := by
  have hrunK : VmState.runK host fuel st = Sum.inr st' :=
    runK_of_script (host := host) (fuel := fuel) (st := st) (res := Sum.inr st') hscript
  simp [VmState.runRaw, hrunK]

theorem run_of_script_halt (host : Host) (fuel : Nat) (st st' : VmState) (exitCode : Int)
    (hscript : RunScript host fuel st (Sum.inl (exitCode, st'))) :
    VmState.run host fuel st = VmState.finalizeHalt exitCode st' := by
  unfold VmState.run VmState.finalizeRunResult
  simp [runRaw_of_script_halt (host := host) (fuel := fuel) (st := st) (st' := st') (exitCode := exitCode)
    hscript]

theorem run_of_script_continue (host : Host) (fuel : Nat) (st st' : VmState)
    (hscript : RunScript host fuel st (Sum.inr st')) :
    VmState.run host fuel st = .halt (Excno.fatal.toInt) st' := by
  have hraw : VmState.runRaw host fuel st = .halt (Excno.fatal.toInt) st' :=
    runRaw_of_script_continue (host := host) (fuel := fuel) (st := st) (st' := st') hscript
  have hnonCommit : ¬ (Excno.fatal.toInt = -1 ∨ Excno.fatal.toInt = -2) := by
    decide
  unfold VmState.run VmState.finalizeRunResult
  rw [hraw]
  simp [VmState.finalizeHalt, hnonCommit]

open Lean Elab Tactic

syntax "vm_simp" : tactic

macro_rules
  | `(tactic| vm_simp) =>
      `(tactic| simp [runRaw_zero, runRaw_succ, runK_zero, runK_succ,
        runRaw_succ_continue, runRaw_succ_halt,
        VmState.run_succ_continue, VmState.run_succ_halt, VmState.run_succ_finalized])

syntax "vm_step" term : tactic
syntax "vm_halt" term : tactic

macro_rules
  | `(tactic| vm_step $h) =>
      `(tactic| refine RunScript.next (by exact $h) ?_)
  | `(tactic| vm_halt $h) =>
      `(tactic| exact RunScript.halted (by exact $h))

syntax "vm_script" "[" term,* "]" : tactic

macro_rules
  | `(tactic| vm_script []) =>
      `(tactic| fail "vm_script requires at least one step lemma")
  | `(tactic| vm_script [$h]) =>
      `(tactic| vm_halt $h)
  | `(tactic| vm_script [$h, $hs,*]) =>
      `(tactic| (vm_step $h; vm_script [$hs,*]))

theorem stepOrdinaryDecode_cp0_of_decode_ok (host : Host) (st : VmState) (code rest : Slice)
    (instr : Instr) (totBits : Nat)
    (hcp : st.cp = 0)
    (hdecode : decodeCp0WithBits code = .ok (instr, totBits, rest)) :
    VmState.stepOrdinaryDecode host st code = VmState.stepOrdinaryOk host st instr totBits rest := by
  simp [VmState.stepOrdinaryDecode, hcp, hdecode]

theorem stepOrdinaryDecode_cp0_of_decode_error (host : Host) (st : VmState) (code : Slice) (e : Excno)
    (hcp : st.cp = 0)
    (hdecode : decodeCp0WithBits code = .error e) :
    VmState.stepOrdinaryDecode host st code = VmState.stepOrdinaryInvalid st code e := by
  simp [VmState.stepOrdinaryDecode, hcp, hdecode]

theorem stepOrdinaryDecode_nonCp0 (host : Host) (st : VmState) (code : Slice)
    (hcp : st.cp ≠ 0) :
    VmState.stepOrdinaryDecode host st code = VmState.stepOrdinaryInvalid st code .invOpcode := by
  simp [VmState.stepOrdinaryDecode, hcp]

def VmState.execProgramStep (host : Host) (instr : Instr) (st : VmState) : StepResult :=
  let stGas := st.consumeGas (instrGas instr 0)
  if decide (stGas.gas.gasRemaining < 0) then
    stGas.outOfGasHalt
  else
    let (res, st1) := (execInstr host instr).run stGas
    match res with
    | .ok _ =>
        if decide (st1.gas.gasRemaining < 0) then
          st1.outOfGasHalt
        else
          .continue st1
    | .error e =>
        if e = .outOfGas then
          st1.outOfGasHalt
        else
          let stExc := st1.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            stExcGas.outOfGasHalt
          else
            .continue stExcGas

def VmState.execProgram (host : Host) (program : List Instr) (st : VmState) : StepResult :=
  match program with
  | [] => .continue st
  | instr :: rest =>
      match VmState.execProgramStep host instr st with
      | .halt exitCode st' => .halt exitCode st'
      | .continue st' => VmState.execProgram host rest st'

end TvmLean
