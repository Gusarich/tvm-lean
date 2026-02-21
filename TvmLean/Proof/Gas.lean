import TvmLean.Proof.VM

namespace TvmLean

structure GasBudget where
  reserve : Int
  deriving Repr

def GasBudget.sufficientFor (budget : GasBudget) (st : VmState) : Prop :=
  budget.reserve ≤ st.gas.gasRemaining

def GasBudget.consume (budget : GasBudget) (amount : Int) : GasBudget :=
  { reserve := budget.reserve - amount }

def programBaseGas : List Instr → Int
  | [] => 0
  | instr :: rest => instrGas instr 0 + programBaseGas rest

def GasBudget.ofProgramBase (program : List Instr) : GasBudget :=
  { reserve := programBaseGas program }

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

theorem gasCheck_eq_false_of_not_lt_zero (n : Int) (h : ¬ n < 0) :
    decide (n < 0) = false := by
  exact decide_eq_false h

theorem consumeGas_check_false (st : VmState) (amount : Int)
    (h : ¬ st.gas.gasRemaining - amount < 0) :
    decide ((st.consumeGas amount).gas.gasRemaining < 0) = false := by
  simpa [VmState.consumeGas, GasLimits.consume] using decide_eq_false h

theorem GasBudget.precheck_false (budget : GasBudget) (st : VmState)
    (hsufficient : budget.sufficientFor st) :
    decide (st.gas.gasRemaining < budget.reserve) = false := by
  exact decide_eq_false (Int.not_lt_of_ge hsufficient)

theorem GasBudget.consume_preserves (budget : GasBudget) (st : VmState) (amount : Int)
    (hsufficient : budget.sufficientFor st) :
    (budget.consume amount).sufficientFor (st.consumeGas amount) := by
  dsimp [GasBudget.sufficientFor, GasBudget.consume] at *
  have hsub : budget.reserve - amount ≤ st.gas.gasRemaining - amount :=
    Int.sub_le_sub_right hsufficient amount
  simpa [VmState.consumeGas, GasLimits.consume] using hsub

theorem GasBudget.consume_check_false (budget : GasBudget) (st : VmState) (amount : Int)
    (hsufficient : budget.sufficientFor st)
    (huse : amount ≤ budget.reserve) :
    decide ((st.consumeGas amount).gas.gasRemaining < 0) = false := by
  have hremain : amount ≤ st.gas.gasRemaining :=
    Int.le_trans huse hsufficient
  have hnonneg : 0 ≤ st.gas.gasRemaining - amount := by
    exact (Int.sub_nonneg).2 hremain
  exact consumeGas_check_false st amount (Int.not_lt_of_ge hnonneg)

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

end TvmLean
