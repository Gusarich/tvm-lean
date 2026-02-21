import TvmLean.Proof.VM

namespace TvmLean

structure GasBudget where
  reserve : Int
  deriving Repr

def GasBudget.sufficientFor (budget : GasBudget) (st : VmState) : Prop :=
  budget.reserve ≤ st.gas.gasRemaining

def GasBudget.consume (budget : GasBudget) (amount : Int) : GasBudget :=
  { reserve := budget.reserve - amount }

def GasBudget.zero : GasBudget :=
  { reserve := 0 }

def GasBudget.ofAmount (amount : Int) : GasBudget :=
  { reserve := amount }

def GasBudget.ofInstr (instr : Instr) : GasBudget :=
  { reserve := instrGas instr 0 }

def GasBudget.combine (lhs rhs : GasBudget) : GasBudget :=
  { reserve := lhs.reserve + rhs.reserve }

def GasBudget.append (lhs rhs : GasBudget) : GasBudget :=
  lhs.combine rhs

def programBaseGas : List Instr → Int
  | [] => 0
  | instr :: rest => instrGas instr 0 + programBaseGas rest

def GasBudget.ofProgramBase (program : List Instr) : GasBudget :=
  { reserve := programBaseGas program }

def GasBudget.ofProgram (program : List Instr) : GasBudget :=
  GasBudget.ofProgramBase program

@[simp] theorem GasBudget.zero_reserve :
    GasBudget.zero.reserve = 0 := by
  rfl

@[simp] theorem GasBudget.ofAmount_reserve (amount : Int) :
    (GasBudget.ofAmount amount).reserve = amount := by
  rfl

@[simp] theorem GasBudget.ofInstr_reserve (instr : Instr) :
    (GasBudget.ofInstr instr).reserve = instrGas instr 0 := by
  rfl

@[simp] theorem GasBudget.ofProgramBase_reserve (program : List Instr) :
    (GasBudget.ofProgramBase program).reserve = programBaseGas program := by
  rfl

@[simp] theorem GasBudget.ofProgram_eq_ofProgramBase (program : List Instr) :
    GasBudget.ofProgram program = GasBudget.ofProgramBase program := by
  rfl

@[simp] theorem GasBudget.ofProgram_reserve (program : List Instr) :
    (GasBudget.ofProgram program).reserve = programBaseGas program := by
  rfl

@[simp] theorem GasBudget.combine_reserve (lhs rhs : GasBudget) :
    (lhs.combine rhs).reserve = lhs.reserve + rhs.reserve := by
  rfl

@[simp] theorem GasBudget.append_reserve (lhs rhs : GasBudget) :
    (lhs.append rhs).reserve = lhs.reserve + rhs.reserve := by
  rfl

@[simp] theorem programBaseGas_nil :
    programBaseGas [] = 0 := by
  rfl

@[simp] theorem programBaseGas_cons (instr : Instr) (rest : List Instr) :
    programBaseGas (instr :: rest) = instrGas instr 0 + programBaseGas rest := by
  rfl

theorem programBaseGas_append (xs ys : List Instr) :
    programBaseGas (xs ++ ys) = programBaseGas xs + programBaseGas ys := by
  induction xs with
  | nil =>
      simp [programBaseGas]
  | cons x xs ih =>
      simp [programBaseGas, ih, Int.add_assoc]

theorem GasBudget.ofProgramBase_append (xs ys : List Instr) :
    GasBudget.ofProgramBase (xs ++ ys) =
      (GasBudget.ofProgramBase xs).combine (GasBudget.ofProgramBase ys) := by
  simp [GasBudget.ofProgramBase, GasBudget.combine, programBaseGas_append]

theorem GasBudget.ofProgram_append (xs ys : List Instr) :
    GasBudget.ofProgram (xs ++ ys) =
      (GasBudget.ofProgram xs).combine (GasBudget.ofProgram ys) := by
  simpa [GasBudget.ofProgram] using GasBudget.ofProgramBase_append xs ys

theorem gasCheck_eq_false_of_not_lt_zero (n : Int) (h : ¬ n < 0) :
    decide (n < 0) = false := by
  exact decide_eq_false h

theorem consumeGas_check_false (st : VmState) (amount : Int)
    (h : ¬ st.gas.gasRemaining - amount < 0) :
    decide ((st.consumeGas amount).gas.gasRemaining < 0) = false := by
  simpa [VmState.consumeGas, GasLimits.consume] using decide_eq_false h

theorem consumeGas_check_false_of_le (st : VmState) (amount : Int)
    (h : amount ≤ st.gas.gasRemaining) :
    decide ((st.consumeGas amount).gas.gasRemaining < 0) = false := by
  have hnonneg : 0 ≤ st.gas.gasRemaining - amount :=
    (Int.sub_nonneg).2 h
  exact consumeGas_check_false st amount (Int.not_lt_of_ge hnonneg)

theorem GasBudget.precheck_false (budget : GasBudget) (st : VmState)
    (hsufficient : budget.sufficientFor st) :
    decide (st.gas.gasRemaining < budget.reserve) = false := by
  exact decide_eq_false (Int.not_lt_of_ge hsufficient)

theorem GasBudget.sufficientFor_mono (budget₁ budget₂ : GasBudget) (st : VmState)
    (hbudget : budget₁.reserve ≤ budget₂.reserve)
    (hsufficient : budget₂.sufficientFor st) :
    budget₁.sufficientFor st := by
  exact Int.le_trans hbudget hsufficient

theorem GasBudget.sufficientFor_consumeGas_iff (budget : GasBudget) (st : VmState) (amount : Int) :
    budget.sufficientFor (st.consumeGas amount) ↔
      budget.reserve + amount ≤ st.gas.gasRemaining := by
  constructor
  · intro hsufficient
    have hsub : budget.reserve ≤ st.gas.gasRemaining - amount := by
      simpa [GasBudget.sufficientFor, VmState.consumeGas, GasLimits.consume] using hsufficient
    exact Int.add_le_of_le_sub_right hsub
  · intro hsum
    have hsub : budget.reserve ≤ st.gas.gasRemaining - amount :=
      Int.le_sub_right_of_add_le hsum
    simpa [GasBudget.sufficientFor, VmState.consumeGas, GasLimits.consume] using hsub

theorem GasBudget.sufficientFor_consumeGas_mono (budget : GasBudget) (st : VmState)
    {amount₁ amount₂ : Int} (hamount : amount₁ ≤ amount₂)
    (hsufficient : budget.sufficientFor (st.consumeGas amount₂)) :
    budget.sufficientFor (st.consumeGas amount₁) := by
  have hsum₂ : budget.reserve + amount₂ ≤ st.gas.gasRemaining :=
    (GasBudget.sufficientFor_consumeGas_iff budget st amount₂).1 hsufficient
  have hsum₁ : budget.reserve + amount₁ ≤ st.gas.gasRemaining := by
    have hmono : budget.reserve + amount₁ ≤ budget.reserve + amount₂ :=
      Int.add_le_add_left hamount budget.reserve
    exact Int.le_trans hmono hsum₂
  exact (GasBudget.sufficientFor_consumeGas_iff budget st amount₁).2 hsum₁

theorem GasBudget.consume_preserves (budget : GasBudget) (st : VmState) (amount : Int)
    (hsufficient : budget.sufficientFor st) :
    (budget.consume amount).sufficientFor (st.consumeGas amount) := by
  dsimp [GasBudget.sufficientFor, GasBudget.consume] at *
  have hsub : budget.reserve - amount ≤ st.gas.gasRemaining - amount :=
    Int.sub_le_sub_right hsufficient amount
  simpa [VmState.consumeGas, GasLimits.consume] using hsub

@[simp] theorem GasBudget.consume_add (budget : GasBudget) (a b : Int) :
    budget.consume (a + b) = (budget.consume a).consume b := by
  cases budget with
  | mk reserve =>
      simp [GasBudget.consume, Int.sub_sub]

theorem GasBudget.sufficientFor_split_left (left right : GasBudget) (st : VmState)
    (hsufficient : (left.combine right).sufficientFor st) :
    left.sufficientFor (st.consumeGas right.reserve) := by
  have hsum : left.reserve + right.reserve ≤ st.gas.gasRemaining := by
    simpa [GasBudget.sufficientFor, GasBudget.combine] using hsufficient
  exact (GasBudget.sufficientFor_consumeGas_iff left st right.reserve).2 hsum

theorem GasBudget.sufficientFor_split_right (left right : GasBudget) (st : VmState)
    (hsufficient : (left.combine right).sufficientFor st) :
    right.sufficientFor (st.consumeGas left.reserve) := by
  have hsum : right.reserve + left.reserve ≤ st.gas.gasRemaining := by
    dsimp [GasBudget.sufficientFor, GasBudget.combine] at hsufficient
    simpa [Int.add_comm, Int.add_left_comm, Int.add_assoc] using hsufficient
  exact (GasBudget.sufficientFor_consumeGas_iff right st left.reserve).2 hsum

theorem GasBudget.combine_sufficient_of_split_left (left right : GasBudget) (st : VmState)
    (hsufficient : left.sufficientFor (st.consumeGas right.reserve)) :
    (left.combine right).sufficientFor st := by
  have hsum : left.reserve + right.reserve ≤ st.gas.gasRemaining :=
    (GasBudget.sufficientFor_consumeGas_iff left st right.reserve).1 hsufficient
  simpa [GasBudget.sufficientFor, GasBudget.combine] using hsum

theorem GasBudget.combine_sufficient_of_split_right (left right : GasBudget) (st : VmState)
    (hsufficient : right.sufficientFor (st.consumeGas left.reserve)) :
    (left.combine right).sufficientFor st := by
  have hsum : right.reserve + left.reserve ≤ st.gas.gasRemaining :=
    (GasBudget.sufficientFor_consumeGas_iff right st left.reserve).1 hsufficient
  have hsum' : left.reserve + right.reserve ≤ st.gas.gasRemaining := by
    simpa [Int.add_comm, Int.add_left_comm, Int.add_assoc] using hsum
  simpa [GasBudget.sufficientFor, GasBudget.combine] using hsum'

theorem GasBudget.consume_check_false (budget : GasBudget) (st : VmState) (amount : Int)
    (hsufficient : budget.sufficientFor st)
    (huse : amount ≤ budget.reserve) :
    decide ((st.consumeGas amount).gas.gasRemaining < 0) = false := by
  have hremain : amount ≤ st.gas.gasRemaining :=
    Int.le_trans huse hsufficient
  have hnonneg : 0 ≤ st.gas.gasRemaining - amount := by
    exact (Int.sub_nonneg).2 hremain
  exact consumeGas_check_false st amount (Int.not_lt_of_ge hnonneg)

theorem GasBudget.consume_self_check_false (budget : GasBudget) (st : VmState)
    (hsufficient : budget.sufficientFor st) :
    decide ((st.consumeGas budget.reserve).gas.gasRemaining < 0) = false := by
  exact consumeGas_check_false_of_le st budget.reserve hsufficient

theorem GasBudget.ofProgram_check_false (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram program).sufficientFor st) :
    decide (st.gas.gasRemaining < programBaseGas program) = false := by
  simpa using GasBudget.precheck_false (budget := GasBudget.ofProgram program) (st := st) hsufficient

theorem GasBudget.ofProgram_prefix_sufficient_of_append
    (pref suff : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram (pref ++ suff)).sufficientFor st) :
    (GasBudget.ofProgram pref).sufficientFor (st.consumeGas (programBaseGas suff)) := by
  have hcombined :
      ((GasBudget.ofProgram pref).combine (GasBudget.ofProgram suff)).sufficientFor st := by
    change (GasBudget.ofProgramBase (pref ++ suff)).sufficientFor st at hsufficient
    change ((GasBudget.ofProgramBase pref).combine (GasBudget.ofProgramBase suff)).sufficientFor st
    simpa [GasBudget.ofProgramBase_append] using hsufficient
  have hsplit :
      (GasBudget.ofProgram pref).sufficientFor
        (st.consumeGas (GasBudget.ofProgram suff).reserve) :=
    GasBudget.sufficientFor_split_left
      (left := GasBudget.ofProgram pref)
      (right := GasBudget.ofProgram suff)
      (st := st)
      hcombined
  simpa using hsplit

theorem GasBudget.ofProgram_suffix_sufficient_of_append
    (pref suff : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram (pref ++ suff)).sufficientFor st) :
    (GasBudget.ofProgram suff).sufficientFor (st.consumeGas (programBaseGas pref)) := by
  have hcombined :
      ((GasBudget.ofProgram pref).combine (GasBudget.ofProgram suff)).sufficientFor st := by
    change (GasBudget.ofProgramBase (pref ++ suff)).sufficientFor st at hsufficient
    change ((GasBudget.ofProgramBase pref).combine (GasBudget.ofProgramBase suff)).sufficientFor st
    simpa [GasBudget.ofProgramBase_append] using hsufficient
  have hsplit :
      (GasBudget.ofProgram suff).sufficientFor
        (st.consumeGas (GasBudget.ofProgram pref).reserve) :=
    GasBudget.sufficientFor_split_right
      (left := GasBudget.ofProgram pref)
      (right := GasBudget.ofProgram suff)
      (st := st)
      hcombined
  simpa using hsplit

theorem GasBudget.ofProgram_prefix_check_false_of_append
    (pref suff : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram (pref ++ suff)).sufficientFor st) :
    decide ((st.consumeGas (programBaseGas suff)).gas.gasRemaining < programBaseGas pref) = false := by
  exact GasBudget.ofProgram_check_false
    (program := pref)
    (st := st.consumeGas (programBaseGas suff))
    (GasBudget.ofProgram_prefix_sufficient_of_append
      (pref := pref)
      (suff := suff)
      (st := st)
      hsufficient)

theorem GasBudget.ofProgram_suffix_check_false_of_append
    (pref suff : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram (pref ++ suff)).sufficientFor st) :
    decide ((st.consumeGas (programBaseGas pref)).gas.gasRemaining < programBaseGas suff) = false := by
  exact GasBudget.ofProgram_check_false
    (program := suff)
    (st := st.consumeGas (programBaseGas pref))
    (GasBudget.ofProgram_suffix_sufficient_of_append
      (pref := pref)
      (suff := suff)
      (st := st)
      hsufficient)

theorem GasBudget.ofInstr_check_false (instr : Instr) (st : VmState)
    (hsufficient : (GasBudget.ofInstr instr).sufficientFor st) :
    decide ((st.consumeGas (instrGas instr 0)).gas.gasRemaining < 0) = false := by
  simpa [GasBudget.ofInstr] using
    (GasBudget.consume_self_check_false (budget := GasBudget.ofInstr instr) (st := st) hsufficient)

theorem VmState.execProgramStep_no_pre_out_of_gas (host : Host) (instr : Instr) (st : VmState)
    (hsufficient : (GasBudget.ofInstr instr).sufficientFor st) :
    VmState.execProgramStep host instr st =
      let stGas := st.consumeGas (instrGas instr 0)
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
              .continue stExcGas := by
  have hcost : instrGas instr 0 ≤ st.gas.gasRemaining := by
    simpa [GasBudget.ofInstr, GasBudget.sufficientFor] using hsufficient
  have hpre : ¬ st.gas.gasRemaining - instrGas instr 0 < 0 := by
    exact Int.not_lt_of_ge ((Int.sub_nonneg).2 hcost)
  unfold VmState.execProgramStep
  simp [VmState.consumeGas, GasLimits.consume, hpre]
  rfl

def consumeProgramBaseGas : List Instr → VmState → VmState
  | [], st => st
  | instr :: rest, st =>
      consumeProgramBaseGas rest (st.consumeGas (instrGas instr 0))

@[simp] theorem consumeProgramBaseGas_nil (st : VmState) :
    consumeProgramBaseGas [] st = st := by
  rfl

@[simp] theorem consumeProgramBaseGas_cons (instr : Instr) (rest : List Instr) (st : VmState) :
    consumeProgramBaseGas (instr :: rest) st =
      consumeProgramBaseGas rest (st.consumeGas (instrGas instr 0)) := by
  rfl

theorem consumeProgramBaseGas_append (xs ys : List Instr) (st : VmState) :
    consumeProgramBaseGas (xs ++ ys) st = consumeProgramBaseGas ys (consumeProgramBaseGas xs st) := by
  induction xs generalizing st with
  | nil =>
      simp [consumeProgramBaseGas]
  | cons x xs ih =>
      simp [consumeProgramBaseGas, ih]

theorem consumeProgramBaseGas_gasRemaining (program : List Instr) (st : VmState) :
    (consumeProgramBaseGas program st).gas.gasRemaining =
      st.gas.gasRemaining - programBaseGas program := by
  induction program generalizing st with
  | nil =>
      simp [consumeProgramBaseGas, programBaseGas]
  | cons instr rest ih =>
      simpa [consumeProgramBaseGas, programBaseGas, Int.sub_eq_add_neg,
        Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.neg_add] using
        ih (st := st.consumeGas (instrGas instr 0))

theorem GasBudget.ofProgramBase_post_nonneg (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgramBase program).sufficientFor st) :
    0 ≤ (consumeProgramBaseGas program st).gas.gasRemaining := by
  dsimp [GasBudget.ofProgramBase, GasBudget.sufficientFor] at hsufficient
  have hnonneg : 0 ≤ st.gas.gasRemaining - programBaseGas program := by
    exact (Int.sub_nonneg).2 hsufficient
  simpa [consumeProgramBaseGas_gasRemaining] using hnonneg

theorem GasBudget.ofProgramBase_post_check_false (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgramBase program).sufficientFor st) :
    decide ((consumeProgramBaseGas program st).gas.gasRemaining < 0) = false := by
  exact decide_eq_false (Int.not_lt_of_ge (GasBudget.ofProgramBase_post_nonneg program st hsufficient))

theorem GasBudget.ofProgram_post_nonneg (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram program).sufficientFor st) :
    0 ≤ (consumeProgramBaseGas program st).gas.gasRemaining := by
  simpa [GasBudget.ofProgram] using
    GasBudget.ofProgramBase_post_nonneg (program := program) (st := st) hsufficient

theorem GasBudget.ofProgram_post_check_false (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram program).sufficientFor st) :
    decide ((consumeProgramBaseGas program st).gas.gasRemaining < 0) = false := by
  simpa [GasBudget.ofProgram] using
    GasBudget.ofProgramBase_post_check_false (program := program) (st := st) hsufficient

end TvmLean
