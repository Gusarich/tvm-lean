import TvmLean.Semantics
import TvmLean.Native.Host.StubHost
import Init.Data.Array.Extract

namespace Proofs.ToyCounter

open TvmLean

set_option maxHeartbeats 50000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

-- `native_decide` needs `Decidable (x = y)`; core `Except` doesn't ship a `DecidableEq` instance.
private instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α) :=
  fun x y =>
    match x, y with
    | .ok a, .ok b =>
        match decEq a b with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .error e1, .error e2 =>
        match decEq e1 e2 with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)
    | .ok _, .error _ =>
        isFalse (by intro h; cases h)
    | .error _, .ok _ =>
        isFalse (by intro h; cases h)

-- Cell hashing is irrelevant to this proof, but unfolding it during definitional
-- reductions quickly becomes expensive.
attribute [local irreducible] Cell.hashBytes

abbrev Counter32 := UInt32

structure CounterState where
  c4 : Cell
  deriving Repr

private theorem applyCregsCdata_empty (st : VmState) :
    st.applyCregsCdata OrdCregs.empty OrdCdata.empty = st := by
  -- In this toy contract we always run ordinary continuations with empty `cregs` / `cdata`,
  -- so the entry adjustment is a definitional no-op.
  simp [VmState.applyCregsCdata, OrdCregs.empty, OrdCdata.empty]

@[simp] private theorem registerCellLoad_cc (st : VmState) (c : Cell) :
    (st.registerCellLoad c).cc = st.cc := by
  unfold VmState.registerCellLoad
  -- `registerCellLoad` only updates `loadedCells` and `gas`.
  -- We prove the `cc` projection is unchanged by splitting on the `seen` flag.
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] private theorem registerCellLoad_cp (st : VmState) (c : Cell) :
    (st.registerCellLoad c).cp = st.cp := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] private theorem registerCellLoad_regs (st : VmState) (c : Cell) :
    (st.registerCellLoad c).regs = st.regs := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] private theorem registerCellLoad_gasMax (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasMax = st.gas.gasMax := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] private theorem registerCellLoad_gasLimit (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasLimit = st.gas.gasLimit := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] private theorem registerCellLoad_gasCredit (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasCredit = st.gas.gasCredit := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] private theorem registerCellLoad_gasBase (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasBase = st.gas.gasBase := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] private theorem registerCellLoad_gasRemaining (st : VmState) (c : Cell) :
    (st.registerCellLoad c).gas.gasRemaining =
      st.gas.gasRemaining -
        (if st.loadedCells.any (fun x => x == Cell.hashBytes c) then cellReloadGasPrice else cellLoadGasPrice) := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas, GasLimits.consume]

@[simp] private theorem consumeGas_regs (st : VmState) (amount : Int) :
    (st.consumeGas amount).regs = st.regs := by
  rfl

private theorem consumeGas_maxDataDepth (st : VmState) (amount : Int) :
    (st.consumeGas amount).maxDataDepth = st.maxDataDepth := by
  rfl

private theorem registerCellLoad_maxDataDepth (st : VmState) (c : Cell) :
    (st.registerCellLoad c).maxDataDepth = st.maxDataDepth := by
  unfold VmState.registerCellLoad
  cases hSeen : st.loadedCells.any (fun x => x == Cell.hashBytes c) <;>
    simp [hSeen, VmState.consumeGas]

@[simp] private theorem tryCommit_regs (st : VmState) :
    (st.tryCommit).2.regs = st.regs := by
  -- `tryCommit` only updates `cstate` on success; registers are preserved.
  unfold VmState.tryCommit
  by_cases h : st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth <;>
    simp [h]

-- Avoid unfolding `applyCregsCdata` in step-by-step execution proofs; rewrite the
-- empty case via `applyCregsCdata_empty` instead.
attribute [local irreducible] VmState.applyCregsCdata

def encodeCounter (n : Nat) : Cell :=
  (Builder.empty.storeBits (natToBits n 32)).finalize

@[simp] theorem encodeCounter_special (n : Nat) : (encodeCounter n).special = false := by
  simp [encodeCounter, Builder.empty, Builder.storeBits, Builder.finalize, Cell.mkOrdinary]

@[simp] private theorem encodeCounter_refs (n : Nat) : (encodeCounter n).refs = #[] := by
  simp [encodeCounter, Builder.empty, Builder.storeBits, Builder.finalize, Cell.mkOrdinary]

def decodeCounter (c : Cell) : Except Excno Nat :=
  if c.bits.size = 32 ∧ c.refs.size = 0 then
    .ok (bitsToNat c.bits)
  else
    .error .cellUnd

def init (x : Counter32) : CounterState :=
  { c4 := encodeCounter x.toNat }

def encodedInputValue (x : Counter32) : Nat :=
  bitsToNat (natToBits x.toNat 32)

def runToyContract (st : CounterState) : Except Excno CounterState := do
  let x ← decodeCounter st.c4
  let x' := (x + 1) % (2 ^ 32)
  return { st with c4 := encodeCounter x' }

def toyCounterProgram : List Instr :=
  [ .pushCtr 4
  , .ctos
  , .ldu 32
  , .pop 0
  , .inc
  , .pushInt (.num 32)
  , .arithExt (.shrMod false false 2 (-1) false none)
  , .newc
  , .stu 32
  , .endc
  , .popCtr 4
  ]

def toyCounterCodeBits : BitString :=
  -- PUSHCTR c4
  natToBits 0xed44 16 ++
  -- CTOS
  natToBits 0xd0 8 ++
  -- LDU 32
  natToBits 0xd3 8 ++ natToBits 31 8 ++
  -- POP s0
  natToBits 0x30 8 ++
  -- INC
  natToBits 0xa4 8 ++
  -- PUSHINT 32
  natToBits 0x80 8 ++ natToBits 0x20 8 ++
  -- MODPOW2 32 (SHRMOD d=2, round=-1)
  natToBits 0xa928 16 ++
  -- NEWC
  natToBits 0xc8 8 ++
  -- STU 32
  natToBits 0xcb 8 ++ natToBits 31 8 ++
  -- ENDC
  natToBits 0xc9 8 ++
  -- POPCTR c4
  natToBits 0xed54 16

def toyCounterCode : Cell :=
  Cell.mkOrdinary toyCounterCodeBits #[]

-- Code positions (bit offsets) for each instruction.
private def code0 : Slice := Slice.ofCell toyCounterCode
private def code1 : Slice := code0.advanceBits 16
private def code2 : Slice := code1.advanceBits 8
private def code3 : Slice := code2.advanceBits 16
private def code4 : Slice := code3.advanceBits 8
private def code5 : Slice := code4.advanceBits 8
private def code6 : Slice := code5.advanceBits 16
private def code7 : Slice := code6.advanceBits 16
private def code8 : Slice := code7.advanceBits 8
private def code9 : Slice := code8.advanceBits 16
private def code10 : Slice := code9.advanceBits 8
private def code11 : Slice := code10.advanceBits 16

-- Precomputed slice bounds: prevents `simp` from unfolding `toyCounterCodeBits.size`
-- just to decide the `if code.bitsRemaining == 0` guard in `VmState.step`.
@[simp] private theorem bitsRemaining_code0 : (code0.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code1 : (code1.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code2 : (code2.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code3 : (code3.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code4 : (code4.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code5 : (code5.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code6 : (code6.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code7 : (code7.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code8 : (code8.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code9 : (code9.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code10 : (code10.bitsRemaining == 0) = false := by native_decide
@[simp] private theorem bitsRemaining_code11 : (code11.bitsRemaining == 0) = true := by native_decide

@[simp] private theorem refsRemaining_code11 : (code11.refsRemaining == 0) = true := by
  -- The contract code cell has no references; advancing the slice doesn't change `refPos`.
  simp [code11, code10, code9, code8, code7, code6, code5, code4, code3, code2, code1, code0,
    Slice.refsRemaining, Slice.advanceBits, Slice.ofCell, toyCounterCode, Cell.mkOrdinary]

-- `VmState.initial toyCounterCode ...` uses `Slice.ofCell toyCounterCode`, not the local `code0` name.
@[simp] private theorem bitsRemaining_ofCell_toyCounterCode :
    ((Slice.ofCell toyCounterCode).bitsRemaining == 0) = false := by
  simpa [code0] using bitsRemaining_code0

-- Prevent `simp` from unfolding `bitsRemaining` into a huge `toyCounterCodeBits.size` computation.
-- We want it to use the cached lemmas above instead.
attribute [local irreducible] Slice.bitsRemaining Slice.refsRemaining

/-!
Proof-engineering helper: rewrite the big `execInstr` dispatch chain to a tiny
handler for the opcodes used by the toy counter contract.

This keeps the end-to-end proof focused on the real interpreter, but avoids
repeatedly unfolding every dispatch layer (`execInstrStack`, `execInstrCont`, …)
at each step.
-/
private def execInstrToy : Instr → VM Unit
  | .pushCtr 4 =>
      execInstrContPushCtr (.pushCtr 4) (pure ())
  | .ctos =>
      execInstrCellCtos .ctos (pure ())
  | .ldu 32 =>
      execInstrCellLdu (.ldu 32) (pure ())
  | .pop 0 =>
      execInstrStackPop (.pop 0) (pure ())
  | .inc =>
      execInstrArithInc .inc (pure ())
  | .pushInt (.num 32) =>
      execInstrStackPushInt (.pushInt (.num 32)) (pure ())
  | .arithExt (.shrMod false false 2 (-1) false none) =>
      execInstrArithExt (.arithExt (.shrMod false false 2 (-1) false none)) (pure ())
  | .newc =>
      execInstrCellNewc .newc (pure ())
  | .stu 32 =>
      execInstrCellStu (.stu 32) (pure ())
  | .endc =>
      execInstrCellEndc .endc (pure ())
  | .popCtr 4 =>
      execInstrContPopCtr (.popCtr 4) (pure ())
  | i =>
      VM.unimplementedInstr { name := Instr.pretty i } "toyCounter: unexpected opcode"

@[simp] private theorem execInstr_pushCtr4 :
    execInstr stubHost (.pushCtr 4) = execInstrToy (.pushCtr 4) := by
  rfl

@[simp] private theorem execInstr_run_pushCtr4 (st : VmState) :
    (execInstr stubHost (.pushCtr 4)).run st =
      (.ok (), { st with stack := st.stack.push (.cell st.regs.c4) }) := by
  -- Reduce through the tiny `execInstrToy` dispatcher and the `PUSHCTR` handler.
  simp [execInstrToy, execInstrContPushCtr, VM.push, VmState.getCtr, ExceptT.run]
  rfl

@[simp] private theorem execInstr_ctos :
    execInstr stubHost .ctos = execInstrToy .ctos := by
  rfl

@[simp] private theorem execInstr_ldu32 :
    execInstr stubHost (.ldu 32) = execInstrToy (.ldu 32) := by
  rfl

@[simp] private theorem execInstr_pop0 :
    execInstr stubHost (.pop 0) = execInstrToy (.pop 0) := by
  rfl

@[simp] private theorem execInstr_inc :
    execInstr stubHost .inc = execInstrToy .inc := by
  rfl

@[simp] private theorem execInstr_pushInt32 :
    execInstr stubHost (.pushInt (.num 32)) = execInstrToy (.pushInt (.num 32)) := by
  rfl

@[simp] private theorem execInstr_modPow2_32 :
    execInstr stubHost (.arithExt (.shrMod false false 2 (-1) false none)) =
      execInstrToy (.arithExt (.shrMod false false 2 (-1) false none)) := by
  rfl

@[simp] private theorem execInstr_newc :
    execInstr stubHost .newc = execInstrToy .newc := by
  rfl

@[simp] private theorem execInstr_stu32 :
    execInstr stubHost (.stu 32) = execInstrToy (.stu 32) := by
  rfl

@[simp] private theorem execInstr_endc :
    execInstr stubHost .endc = execInstrToy .endc := by
  rfl

@[simp] private theorem execInstr_popCtr4 :
    execInstr stubHost (.popCtr 4) = execInstrToy (.popCtr 4) := by
  rfl

-- Avoid repeatedly unfolding the cp0 decoder in per-step proofs.
@[simp] private theorem decode_code0 :
    decodeCp0WithBits code0 = .ok (.pushCtr 4, 16, code1) := by
  rfl

-- Bridge lemma: the initial state's code slice is `Slice.ofCell toyCounterCode`.
@[simp] private theorem decode_ofCell_toyCounterCode :
    decodeCp0WithBits (Slice.ofCell toyCounterCode) = .ok (.pushCtr 4, 16, code1) := by
  simpa [code0] using decode_code0

@[simp] private theorem decode_code1 :
    decodeCp0WithBits code1 = .ok (.ctos, 8, code2) := by
  rfl

@[simp] private theorem decode_code2 :
    decodeCp0WithBits code2 = .ok (.ldu 32, 16, code3) := by
  rfl

@[simp] private theorem decode_code3 :
    decodeCp0WithBits code3 = .ok (.pop 0, 8, code4) := by
  rfl

@[simp] private theorem decode_code4 :
    decodeCp0WithBits code4 = .ok (.inc, 8, code5) := by
  rfl

@[simp] private theorem decode_code5 :
    decodeCp0WithBits code5 = .ok (.pushInt (.num 32), 16, code6) := by
  rfl

@[simp] private theorem decode_code6 :
    decodeCp0WithBits code6 = .ok (.arithExt (.shrMod false false 2 (-1) false none), 16, code7) := by
  have hhave16 : code6.haveBits 16 = true := by
    native_decide
  have hw16 : bitsToNat (code6.readBits 16) = 0xa928 := by
    native_decide
  have hRange16 :
      (0xa920 ≤ bitsToNat (code6.readBits 16) ∧ bitsToNat (code6.readBits 16) ≤ 0xa92e) ∨
        (0xa9a0 ≤ bitsToNat (code6.readBits 16) ∧ bitsToNat (code6.readBits 16) ≤ 0xa9ae) ∨
        (0xa9c0 ≤ bitsToNat (code6.readBits 16) ∧ bitsToNat (code6.readBits 16) ≤ 0xa9ce) := by
    simpa [hw16] using (show
      (0xa920 ≤ (0xa928 : Nat) ∧ (0xa928 : Nat) ≤ 0xa92e) ∨
        (0xa9a0 ≤ (0xa928 : Nat) ∧ (0xa928 : Nat) ≤ 0xa9ae) ∨
        (0xa9c0 ≤ (0xa928 : Nat) ∧ (0xa928 : Nat) ≤ 0xa9ce) from by decide)
  have hb8 :
      decodeCp0WithBits_b8 code6 0xa9 =
        .ok (.arithExt (.shrMod false false 2 (-1) false none), 16, code7) := by
    simpa [code7] using decodeCp0WithBits_b8_a928 (s := code6) hhave16 hw16
  have hstage :
      decodeCp0_a9_fixed16 code6 =
        .ok (some (.arithExt (.shrMod false false 2 (-1) false none), 16, code7)) := by
    unfold decodeCp0_a9_fixed16
    rw [hhave16, hw16]
    simp [hRange16]
    rw [hb8]
    rfl
  have htry :
      decodeCp0TryStages code6
        [ decodeCp0_a9_fixed16
        , decodeCp0_decode4
        , decodeCp0_decode10
        , decodeCp0_decode13
        , decodeCp0_decode24
        , decodeCp0_decode16
        , decodeCp0_decode18
        , decodeCp0_decode15
        , decodeCp0_decode14
        , decodeCp0_decode48
        , decodeCp0_decode8
        ] = .ok (some (.arithExt (.shrMod false false 2 (-1) false none), 16, code7)) := by
    unfold decodeCp0TryStages
    simp [hstage]
    rfl
  unfold decodeCp0WithBits
  rw [htry]
  rfl

@[simp] private theorem decode_code7 :
    decodeCp0WithBits code7 = .ok (.newc, 8, code8) := by
  rfl

@[simp] private theorem decode_code8 :
    decodeCp0WithBits code8 = .ok (.stu 32, 16, code9) := by
  rfl

@[simp] private theorem decode_code9 :
    decodeCp0WithBits code9 = .ok (.endc, 8, code10) := by
  rfl

@[simp] private theorem decode_code10 :
    decodeCp0WithBits code10 = .ok (.popCtr 4, 16, code11) := by
  rfl

-- From this point on, per-step proofs should only use the cached decode lemmas above.
attribute [local irreducible] decodeCp0WithBits

-- Prevent `simp`/reduction from unfolding the huge `execInstr` dispatcher; use the
-- small `execInstrToy` rewrite lemmas instead.
attribute [local irreducible] execInstr

-- Keep the bytecode cell opaque during execution proofs; unfolding `toyCounterCodeBits`
-- generates large terms that drown `simp`/`dsimp`.
attribute [local irreducible] toyCounterCodeBits toyCounterCode

-- `VmState.stepOrdinary` is now split into helpers; keep the unused branches opaque in this proof.
attribute [local irreducible] VmState.stepOrdinaryInvalid

private def extractCounterState (res : StepResult) : Except Excno CounterState :=
  match res with
  | .halt exitCode stF =>
      if exitCode = -1 ∨ exitCode = -2 then
        .ok { c4 := stF.regs.c4 }
      else
        .error .fatal
  | .continue _ =>
      .error .fatal

def runToyCounter (st : CounterState) : Except Excno CounterState :=
  let st0 := VmState.initial toyCounterCode GasLimits.infty
  let st1 := { st0 with regs := { st0.regs with c4 := st.c4 } }
  extractCounterState (VmState.finalizeRunResult (VmState.runRaw stubHost 50 st1))

def resultNat (r : Except Excno Nat) : Option Nat :=
  match r with
  | .ok n => some n
  | .error _ => none

private def bitStep (acc : Nat) (b : Bool) : Nat :=
  (acc <<< 1) + (if b then 1 else 0)

private theorem bitStep_lt_pow2_succ {acc k : Nat} (hacc : acc < 2 ^ k) (b : Bool) :
    bitStep acc b < 2 ^ (k + 1) := by
  have hacc' : acc ≤ (2 ^ k).pred := Nat.le_pred_of_lt hacc
  have hmul : 2 * acc ≤ 2 * (2 ^ k).pred := Nat.mul_le_mul_left 2 hacc'
  have hbit : (if b then 1 else 0) ≤ 1 := by
    cases b <;> decide
  have hsum : 2 * acc + (if b then 1 else 0) ≤ 2 * acc + 1 :=
    Nat.add_le_add_left hbit (2 * acc)
  have hle : 2 * acc + 1 ≤ 2 * (2 ^ k).pred + 1 :=
    Nat.add_le_add_right hmul 1
  have hkpos : 0 < 2 ^ k :=
    Nat.pow_pos (a := 2) (n := k) (by decide)
  have hpred_succ : (2 ^ k).pred.succ = 2 ^ k :=
    Nat.succ_pred_eq_of_pos hkpos
  have hpred_add_one : (2 ^ k).pred + 1 = 2 ^ k := by
    simpa [Nat.succ_eq_add_one] using hpred_succ
  have hlt : 2 * (2 ^ k).pred + 1 < 2 ^ (k + 1) := by
    have hlt' : 2 * (2 ^ k).pred + 1 < 2 * (2 ^ k).pred + 2 := by
      simpa [Nat.add_assoc] using Nat.lt_succ_self (2 * (2 ^ k).pred + 1)
    -- Rewrite the RHS: 2*pred + 2 = 2*(pred+1) = 2*2^k = 2^(k+1).
    have hR : 2 * (2 ^ k).pred + 2 = 2 ^ (k + 1) := by
      calc
        2 * (2 ^ k).pred + 2 = 2 * ((2 ^ k).pred + 1) := by
          have : 2 * ((2 ^ k).pred + 1) = 2 * (2 ^ k).pred + 2 := by
            simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          exact this.symm
        _ = 2 * (2 ^ k) := by
          rw [hpred_add_one]
        _ = 2 ^ (k + 1) := by
          -- `2^(k+1) = 2^k * 2`.
          simpa [Nat.pow_succ, Nat.mul_comm]
    -- Avoid `simp` rewriting `pred` into subtraction: rewrite the goal directly.
    rw [← hR]
    exact hlt'
  have hle' : 2 * acc + (if b then 1 else 0) ≤ 2 * (2 ^ k).pred + 1 :=
    Nat.le_trans hsum hle
  have : 2 * acc + (if b then 1 else 0) < 2 ^ (k + 1) :=
    Nat.lt_of_le_of_lt hle' hlt
  simpa [bitStep, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_assoc, Nat.add_assoc] using this

private theorem foldl_bitStep_lt_pow2 (l : List Bool) (acc k : Nat) (hacc : acc < 2 ^ k) :
    List.foldl bitStep acc l < 2 ^ (k + l.length) := by
  induction l generalizing acc k with
  | nil =>
      simpa using hacc
  | cons b tl ih =>
      have hstep : bitStep acc b < 2 ^ (k + 1) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bitStep_lt_pow2_succ (k := k) hacc b
      have := ih (acc := bitStep acc b) (k := k + 1) hstep
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

theorem bitsToNat_lt_pow2 (bs : BitString) :
    bitsToNat bs < 2 ^ bs.size := by
  cases bs with
  | mk l =>
      -- Reduce `bitsToNat` for list-backed arrays.
      simpa [bitsToNat, bitStep] using foldl_bitStep_lt_pow2 l 0 0 (by simp)

theorem modPow2Round_ofNat (n bits : Nat) :
    modPow2Round (Int.ofNat n) bits (-1) = Int.ofNat (n % (2 ^ bits)) := by
  by_cases hbits : bits = 0
  · subst hbits
    simp [modPow2Round, rshiftPow2Round, floorDivPow2, intPow2]
  · unfold modPow2Round rshiftPow2Round floorDivPow2 intPow2
    simp [hbits, Int.emod_def, Int.mul_comm, Int.mul_assoc, Int.natCast_emod]

theorem intPow2_eq_ofNat (bits : Nat) : intPow2 bits = (Int.ofNat (2 ^ bits)) := by
  unfold intPow2
  induction bits with
  | zero =>
      simp
  | succ bits ih =>
      -- `(2:Int)^(n+1) = (2:Int)^n * 2`, and `2^(n+1) = 2^n * 2`.
      calc
        (2 : Int) ^ (bits + 1) = (2 : Int) ^ bits * (2 : Int) := by
          simpa using (Int.pow_succ (b := (2 : Int)) (e := bits))
        _ = (Int.ofNat (2 ^ bits)) * (2 : Int) := by
          simpa using congrArg (fun t => t * (2 : Int)) ih
        _ = Int.ofNat ((2 ^ bits) * 2) := by
          simpa using (Int.natCast_mul (2 ^ bits) 2).symm
        _ = Int.ofNat (2 ^ (bits + 1)) := by
          simp [Nat.pow_succ]

private theorem signedFits257_ofNat_lt_pow256 (n : Nat) (hn : n < 2 ^ 256) :
    IntVal.signedFits257 (.num (Int.ofNat n)) = true := by
  unfold IntVal.signedFits257
  apply decide_eq_true
  constructor
  · have hPow : (0 : Int) ≤ (2 : Int) ^ (256 : Nat) :=
      Int.pow_nonneg (n := (2 : Int)) (m := 256) (by decide)
    have hLo : -((2 : Int) ^ (256 : Nat)) ≤ (0 : Int) := by
      have : (0 : Int) ≤ (2 : Int) ^ (256 : Nat) ↔ -((2 : Int) ^ (256 : Nat)) ≤ (0 : Int) := by
        simpa [Int.neg_neg] using (Int.neg_nonneg (a := -((2 : Int) ^ (256 : Nat))))
      exact this.mp hPow
    exact Int.le_trans hLo (Int.natCast_nonneg n)
  · have hR : (Int.ofNat (2 ^ 256)) = (2 : Int) ^ (256 : Nat) := by
      simpa [intPow2] using (intPow2_eq_ofNat 256).symm
    have : (Int.ofNat n) < (Int.ofNat (2 ^ 256)) :=
      Int.ofNat_lt.mpr hn
    simpa [hR] using this

private theorem mod32_nonneg_and_lt_intPow2 (n : Nat) :
    ¬ (Int.ofNat (n % (2 ^ 32)) < 0 ∨ Int.ofNat (n % (2 ^ 32)) ≥ intPow2 32) := by
  have hNat : (n % (2 ^ 32)) < 2 ^ 32 := by
    exact Nat.mod_lt n (Nat.pow_pos (a := 2) (n := 32) (by decide))
  have hNonneg : (0 : Int) ≤ Int.ofNat (n % (2 ^ 32)) :=
    Int.natCast_nonneg (n % (2 ^ 32))
  have hLt : Int.ofNat (n % (2 ^ 32)) < intPow2 32 := by
    have hPow : intPow2 32 = (Int.ofNat (2 ^ 32)) := intPow2_eq_ofNat 32
    have : Int.ofNat (n % (2 ^ 32)) < Int.ofNat (2 ^ 32) := by
      exact Int.ofNat_lt.mpr hNat
    simpa [hPow] using this
  intro h
  cases h with
  | inl hlt0 =>
      exact (Int.not_lt.mpr hNonneg) hlt0
  | inr hge =>
      exact (Int.not_le_of_gt hLt) hge

theorem decode_encode_32 (n : Nat) :
    decodeCounter (encodeCounter n) = .ok (bitsToNat (natToBits n 32)) := by
  unfold decodeCounter encodeCounter
  simp [Builder.empty, Builder.storeBits, Builder.finalize, Cell.mkOrdinary, natToBits]

-- Debugging aid: if this file ever gets stuck again, enable command tracing here to see
-- which declaration is currently being elaborated.
set_option trace.Elab.command false

theorem runToyContract_eval (x : Counter32) :
    runToyContract (init x) = .ok { c4 := encodeCounter ((encodedInputValue x + 1) % (2 ^ 32)) } := by
  unfold runToyContract init encodedInputValue
  simp [decode_encode_32]
  rfl

/-!
Instruction-by-instruction execution trace for `runToyCounter`.

Keeping each step as a separate lemma avoids building one gigantic inlined proof term,
which is both slow to elaborate and slow for the kernel to check.
-/

private def inputCell (x : Counter32) : Cell :=
  encodeCounter x.toNat

@[simp] private theorem inputCell_bits_size (x : Counter32) :
    (inputCell x).bits.size = 32 := by
  simp [inputCell, encodeCounter, Builder.empty, Builder.storeBits, Builder.finalize, Cell.mkOrdinary, natToBits]

@[simp] private theorem inputSlice_haveBits_32 (x : Counter32) :
    (Slice.ofCell (inputCell x)).haveBits 32 = true := by
  -- Reduce to `decide (32 ≤ 32)` via the `inputCell_bits_size` simp lemma.
  simp [Slice.haveBits, Slice.ofCell]

@[simp] private theorem ofCell_bitPos (c : Cell) : (Slice.ofCell c).bitPos = 0 := by
  rfl

@[simp] private theorem ofCell_refPos (c : Cell) : (Slice.ofCell c).refPos = 0 := by
  rfl

-- Match what `LDU 32` computes: `bitsToNat (Slice.readBits 32)`.
private def xNat (x : Counter32) : Nat :=
  bitsToNat ((Slice.ofCell (inputCell x)).readBits 32)

private def st0 : VmState :=
  VmState.initial toyCounterCode GasLimits.infty

private def st1 (x : Counter32) : VmState :=
  { st0 with regs := { st0.regs with c4 := inputCell x } }

-- Step 0: PUSHCTR c4
private def st1' (x : Counter32) : VmState :=
  { st1 x with cc := .ordinary code1 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st1Gas (x : Counter32) : VmState :=
  (st1' x).consumeGas (instrGas (.pushCtr 4) 16)

private def st2 (x : Counter32) : VmState :=
  let st := st1Gas x
  { st with stack := st.stack.push (.cell (inputCell x)) }

-- Step 1: CTOS
private def st2' (x : Counter32) : VmState :=
  { st2 x with cc := .ordinary code2 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st2Gas (x : Counter32) : VmState :=
  (st2' x).consumeGas (instrGas .ctos 8)

private def st2Pop (x : Counter32) : VmState :=
  let st := st2Gas x
  { st with stack := st.stack.pop }

private def st2Load (x : Counter32) : VmState :=
  (st2Pop x).registerCellLoad (inputCell x)

private def st3 (x : Counter32) : VmState :=
  let st := st2Load x
  { st with stack := st.stack.push (.slice (Slice.ofCell (inputCell x))) }

-- Step 2: LDU 32
private def st3' (x : Counter32) : VmState :=
  { st3 x with cc := .ordinary code3 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st3Gas (x : Counter32) : VmState :=
  (st3' x).consumeGas (instrGas (.ldu 32) 16)

private def st3Pop (x : Counter32) : VmState :=
  let st := st3Gas x
  { st with stack := st.stack.pop }

private def st4 (x : Counter32) : VmState :=
  let st := st3Pop x
  { st with
    stack :=
      (st.stack.push (.int (.num (Int.ofNat (xNat x)))))
        |>.push (.slice ({ (Slice.ofCell (inputCell x)) with bitPos := 32 })) }

-- Step 3: POP s0 (drop the slice)
private def st4' (x : Counter32) : VmState :=
  { st4 x with cc := .ordinary code4 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st4Gas (x : Counter32) : VmState :=
  (st4' x).consumeGas (instrGas (.pop 0) 8)

private def st5 (x : Counter32) : VmState :=
  let st := st4Gas x
  { st with stack := #[.int (.num (Int.ofNat (xNat x)))] }

-- Step 4: INC
private def st5' (x : Counter32) : VmState :=
  { st5 x with cc := .ordinary code5 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st5Gas (x : Counter32) : VmState :=
  (st5' x).consumeGas (instrGas .inc 8)

private def st6 (x : Counter32) : VmState :=
  let st := st5Gas x
  { st with stack := #[.int (.num (Int.ofNat (xNat x) + 1))] }

-- Step 5: PUSHINT 32
private def st6' (x : Counter32) : VmState :=
  { st6 x with cc := .ordinary code6 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st6Gas (x : Counter32) : VmState :=
  (st6' x).consumeGas (instrGas (.pushInt (.num 32)) 16)

private def st7 (x : Counter32) : VmState :=
  let st := st6Gas x
  { st with stack := st.stack.push (.int (.num 32)) }

-- Step 6: MODPOW2 32 (via SHRMOD d=2, round=-1)
private def st7' (x : Counter32) : VmState :=
  { st7 x with cc := .ordinary code7 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st7Gas (x : Counter32) : VmState :=
  (st7' x).consumeGas (instrGas (.arithExt (.shrMod false false 2 (-1) false none)) 16)

private def rInt (x : Counter32) : Int :=
  modPow2Round (Int.ofNat (xNat x) + 1) 32 (-1)

private def st8 (x : Counter32) : VmState :=
  let st := st7Gas x
  { st with stack := #[.int (.num (rInt x))] }

-- Step 7: NEWC
private def st8' (x : Counter32) : VmState :=
  { st8 x with cc := .ordinary code8 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st8Gas (x : Counter32) : VmState :=
  (st8' x).consumeGas (instrGas .newc 8)

private def st9 (x : Counter32) : VmState :=
  let st := st8Gas x
  { st with stack := st.stack.push (.builder Builder.empty) }

-- Step 8: STU 32
private def st9' (x : Counter32) : VmState :=
  { st9 x with cc := .ordinary code9 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st9Gas (x : Counter32) : VmState :=
  (st9' x).consumeGas (instrGas (.stu 32) 16)

private def st10 (x : Counter32) : VmState :=
  let st := st9Gas x
  { st with
    stack :=
      #[.builder
          (Builder.empty.storeBits
            (natToBits (((Int.ofNat (xNat x) + 1) % 4294967296).toNat) 32))] }

-- Step 9: ENDC
private def st10' (x : Counter32) : VmState :=
  { st10 x with cc := .ordinary code10 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st10Gas (x : Counter32) : VmState :=
  (st10' x).consumeGas (instrGas .endc 8)

private def st10Gas2 (x : Counter32) : VmState :=
  (st10Gas x).consumeGas cellCreateGasPrice

private def outCell (x : Counter32) : Cell :=
  encodeCounter (((Int.ofNat (xNat x) + 1) % 4294967296).toNat)

private def st11 (x : Counter32) : VmState :=
  let st := st10Gas2 x
  { st with stack := #[.cell (outCell x)] }

-- Step 10: POPCTR c4
private def st11' (x : Counter32) : VmState :=
  { st11 x with cc := .ordinary code11 (.quit 0) OrdCregs.empty OrdCdata.empty }

private def st11Gas (x : Counter32) : VmState :=
  (st11' x).consumeGas (instrGas (.popCtr 4) 16)

private def st12 (x : Counter32) : VmState :=
  let st := st11Gas x
  { st with stack := #[], regs := { st.regs with c4 := outCell x } }

-- Step 11: implicit RET (end of code)
private def st13 (x : Counter32) : VmState :=
  let st0 := (st12 x).consumeGas implicitRetGasPrice
  { st0 with regs := { st0.regs with c0 := .quit 0 }, cc := .quit 0 }

@[simp] private theorem st5_cc (x : Counter32) :
    (st5 x).cc = .ordinary code4 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st5, st4Gas, st4', VmState.consumeGas]

@[simp] private theorem st4_cc (x : Counter32) :
    (st4 x).cc = .ordinary code3 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st4, st3Pop, st3Gas, st3', VmState.consumeGas]

@[simp] private theorem st4_cp (x : Counter32) : (st4 x).cp = 0 := by
  simp [st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial,
    VmState.consumeGas]

@[simp] private theorem st5_cp (x : Counter32) : (st5 x).cp = 0 := by
  simp [st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0,
    VmState.initial, VmState.consumeGas]

@[simp] private theorem st6_cc (x : Counter32) :
    (st6 x).cc = .ordinary code5 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st6, st5Gas, st5', VmState.consumeGas]

@[simp] private theorem st6_cp (x : Counter32) : (st6 x).cp = 0 := by
  simp [st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas,
    st1', st1, st0, VmState.initial, VmState.consumeGas]

@[simp] private theorem st7_cc (x : Counter32) :
    (st7 x).cc = .ordinary code6 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st7, st6Gas, st6', VmState.consumeGas]

@[simp] private theorem st7_cp (x : Counter32) : (st7 x).cp = 0 := by
  simp [st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas,
    st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas]

@[simp] private theorem st8_cc (x : Counter32) :
    (st8 x).cc = .ordinary code7 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st8, st7Gas, st7', VmState.consumeGas]

@[simp] private theorem st8_cp (x : Counter32) : (st8 x).cp = 0 := by
  simp [st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load,
    st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas]

@[simp] private theorem st9_cc (x : Counter32) :
    (st9 x).cc = .ordinary code8 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st9, st8Gas, st8', VmState.consumeGas]

@[simp] private theorem st9_cp (x : Counter32) : (st9 x).cp = 0 := by
  simp [st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas,
    st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas]

@[simp] private theorem st10_cc (x : Counter32) :
    (st10 x).cc = .ordinary code9 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st10, st9Gas, st9', VmState.consumeGas]

@[simp] private theorem st10_cp (x : Counter32) : (st10 x).cp = 0 := by
  simp [st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4',
    st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial,
    VmState.consumeGas]

@[simp] private theorem st11_cc (x : Counter32) :
    (st11 x).cc = .ordinary code10 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st11, st10Gas2, st10Gas, st10', VmState.consumeGas]

@[simp] private theorem st11_cp (x : Counter32) : (st11 x).cp = 0 := by
  simp [st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6,
    st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1,
    st0, VmState.initial, VmState.consumeGas]

@[simp] private theorem st12_cc (x : Counter32) :
    (st12 x).cc = .ordinary code11 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st12, st11Gas, st11', VmState.consumeGas]

@[simp] private theorem st2_cc (x : Counter32) :
    (st2 x).cc = .ordinary code1 (.quit 0) OrdCregs.empty OrdCdata.empty := by
  simp [st2, st1Gas, st1', VmState.consumeGas]

@[simp] private theorem st2_cp (x : Counter32) : (st2 x).cp = 0 := by
  simp [st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas]

-- Connect the interpreter's `xNat x` with the spec's `encodedInputValue x`.
private theorem readBits_inputCell (x : Counter32) :
    (Slice.ofCell (inputCell x)).readBits 32 = natToBits x.toNat 32 := by
  simp [Slice.readBits, Slice.ofCell, inputCell, encodeCounter, Builder.empty, Builder.storeBits, Builder.finalize,
    Cell.mkOrdinary, natToBits]

private theorem xNat_eq_encodedInputValue (x : Counter32) :
    xNat x = encodedInputValue x := by
  simp [xNat, encodedInputValue, readBits_inputCell]

-- Bounds: `xNat` comes from 32 bits, so it fits comfortably in 257-bit signed.
private theorem xNat_lt_pow32 (x : Counter32) : xNat x < 2 ^ 32 := by
  have : encodedInputValue x < 2 ^ 32 := by
    simpa [encodedInputValue, natToBits] using (bitsToNat_lt_pow2 (natToBits x.toNat 32))
  simpa [xNat_eq_encodedInputValue x] using this

private theorem pow32_lt_pow256 : (2 ^ 32) < 2 ^ 256 := by
  simpa using (Nat.pow_lt_pow_iff_right Nat.one_lt_two).2 (by decide : (32 : Nat) < 256)

private theorem xNat_succ_lt_pow256 (x : Counter32) : xNat x + 1 < 2 ^ 256 := by
  have hle : xNat x + 1 ≤ 2 ^ 32 := Nat.succ_le_of_lt (xNat_lt_pow32 x)
  exact Nat.lt_of_le_of_lt hle pow32_lt_pow256

private theorem incFits (x : Counter32) :
    IntVal.signedFits257 (.num (Int.ofNat (xNat x) + 1)) = true := by
  have hL : (Int.ofNat (xNat x) + 1) = Int.ofNat (xNat x + 1) := by
    simpa [Nat.succ_eq_add_one] using (Int.ofNat_succ (xNat x)).symm
  simpa [hL] using signedFits257_ofNat_lt_pow256 (n := xNat x + 1) (xNat_succ_lt_pow256 x)

private theorem rInt_eq (x : Counter32) :
    rInt x = Int.ofNat ((xNat x + 1) % (2 ^ 32)) := by
  have h : (Int.ofNat (xNat x) + 1) = Int.ofNat (xNat x + 1) := by
    simpa [Nat.succ_eq_add_one] using (Int.ofNat_succ (xNat x)).symm
  unfold rInt
  rw [h]
  simpa using (modPow2Round_ofNat (n := xNat x + 1) (bits := 32))

private theorem modFits (x : Counter32) :
    IntVal.signedFits257 (.num (rInt x)) = true := by
  have hrNat : ((xNat x + 1) % (2 ^ 32)) < 2 ^ 32 := by
    exact Nat.mod_lt (xNat x + 1) (Nat.pow_pos (a := 2) (n := 32) (by decide))
  have hrNat256 : ((xNat x + 1) % (2 ^ 32)) < 2 ^ 256 :=
    Nat.lt_trans hrNat pow32_lt_pow256
  simpa [rInt_eq x] using signedFits257_ofNat_lt_pow256 (n := ((xNat x + 1) % (2 ^ 32))) hrNat256

private theorem decRange (x : Counter32) :
    decide (rInt x < 0 ∨ rInt x ≥ intPow2 32) = false := by
  have hRange : ¬ (rInt x < 0 ∨ rInt x ≥ intPow2 32) := by
    simpa [rInt_eq x] using mod32_nonneg_and_lt_intPow2 (n := xNat x + 1)
  exact decide_eq_false hRange

private theorem modPow2Fits (x : Counter32) :
    IntVal.signedFits257 (.num (modPow2Round (Int.ofNat (xNat x) + 1) 32 (-1))) = true := by
  simpa [rInt] using modFits x

private theorem modPow2Fits' (x : Counter32) :
    (IntVal.num (modPow2Round (↑(xNat x) + 1) 32 (-1))).signedFits257 = true := by
  simpa using modPow2Fits x

private theorem signedFits257_num32 : (IntVal.num 32).signedFits257 = true := by
  native_decide

private theorem modExpr_toNat (x : Counter32) :
    (((Int.ofNat (xNat x) + 1) % 4294967296).toNat) = ((xNat x + 1) % 4294967296) := by
  have hx : 0 ≤ (Int.ofNat (xNat x) + 1) := by
    exact Int.add_nonneg (Int.natCast_nonneg _) (by decide)
  have hy : 0 ≤ (4294967296 : Int) := by decide
  simpa [Nat.succ_eq_add_one] using (Int.toNat_emod (x := Int.ofNat (xNat x) + 1) (y := 4294967296) hx hy)

private theorem modExpr_decRange (x : Counter32) :
    decide
        (((Int.ofNat (xNat x) + 1) % 4294967296 < 0) ∨
          intPow2 32 ≤ ((Int.ofNat (xNat x) + 1) % 4294967296)) =
      false := by
  have hNonneg : 0 ≤ ((Int.ofNat (xNat x) + 1) % 4294967296) := by
    exact Int.emod_nonneg _ (by decide)
  have hLt : ((Int.ofNat (xNat x) + 1) % 4294967296) < intPow2 32 := by
    have hLt' : ((Int.ofNat (xNat x) + 1) % 4294967296) < (4294967296 : Int) := by
      exact Int.emod_lt_of_pos _ (by decide)
    have hPow : (4294967296 : Int) = intPow2 32 := by
      native_decide
    simpa [hPow] using hLt'
  apply decide_eq_false
  intro h
  cases h with
  | inl hneg =>
      exact (Int.not_lt.mpr hNonneg) hneg
  | inr hge =>
      exact (Int.not_le_of_gt hLt) hge

-- Keep bit-level computations opaque in the execution trace proofs; we only need them via
-- the pre-defined `xNat`/`outCell` shorthands and separate connecting lemmas.
attribute [local irreducible] bitsToNat natToBits

private theorem gas_step0_nonneg :
    ¬ (GasLimits.infty - 26 < 0) := by
  native_decide

private theorem gas_step1_nonneg :
    ¬ (GasLimits.infty - 26 - 18 < 0) := by
  native_decide

private theorem gas_step1_post_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice < 0) := by
  native_decide

private theorem gas_step2_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 < 0) := by
  native_decide

private theorem gas_step3_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 < 0) := by
  native_decide

private theorem gas_step4_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 < 0) := by
  native_decide

private theorem gas_step5_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 < 0) := by
  native_decide

private theorem gas_step6_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 < 0) := by
  native_decide

private theorem gas_step7_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 < 0) := by
  native_decide

private theorem gas_step8_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 < 0) := by
  native_decide

private theorem gas_step9_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 - 18 < 0) := by
  native_decide

private theorem gas_step9_post_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 - 18 - cellCreateGasPrice < 0) := by
  native_decide

private theorem gas_step10_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 - 18 - cellCreateGasPrice - 26 < 0) := by
  native_decide

private theorem gas_step11_nonneg :
    ¬ (GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 - 18 - cellCreateGasPrice - 26 -
      implicitRetGasPrice < 0) := by
  native_decide

@[simp] private theorem vm_pure_run {α : Type} (a : α) (st : VmState) :
    ExceptT.run (pure a : VM α) st = (.ok a, st) := by
  rfl

@[simp] private theorem vm_throw_run {α : Type} (e : Excno) (st : VmState) :
    ExceptT.run (throw e : VM α) st = (.error e, st) := by
  rfl

@[simp] private theorem vm_get_run (st : VmState) :
    ExceptT.run (get : VM VmState) st = (.ok st, st) := by
  rfl

@[simp] private theorem vm_modify_run (f : VmState → VmState) (st : VmState) :
    ExceptT.run (modify f : VM Unit) st = (.ok (), f st) := by
  rfl

@[simp] private theorem vm_set_run (st st' : VmState) :
    ExceptT.run (set st' : VM Unit) st = (.ok (), st') := by
  rfl

@[simp] private theorem vm_bind_run {α β : Type} (mx : VM α) (f : α → VM β) (st : VmState) :
    ExceptT.run (mx >>= f) st =
      match ExceptT.run mx st with
      | (.ok a, st') => ExceptT.run (f a) st'
      | (.error e, st') => (.error e, st') := by
  change StateT.run (ExceptT.run mx >>= ExceptT.bindCont f) st = _
  rw [StateT.run_bind]
  cases h : mx st with
  | mk res st' =>
      cases res with
      | ok a =>
          simp [ExceptT.run, StateT.run, h, ExceptT.bindCont, bind, Bind.bind]
      | error e =>
          simp [ExceptT.run, StateT.run, h, ExceptT.bindCont, bind, Bind.bind]
          rfl

private theorem execInstrToy_run_pop0_st4Gas (x : Counter32) :
    (execInstrToy (.pop 0)).run (st4Gas x) = (.ok (), st5 x) := by
  dsimp [st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0,
    VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrStackPop
    , VM.swap
    , VM.pop
    , VmState.consumeGas
    , GasLimits.consume
    , GasLimits.ofLimits
    , instrGas
    , gasPerInstr
    ]
  try rfl

private theorem execInstrToy_run_inc_st5Gas (x : Counter32) :
    (execInstrToy .inc).run (st5Gas x) = (.ok (), st6 x) := by
  have hIncFits : (IntVal.num (Int.ofNat (xNat x) + 1)).signedFits257 = true := incFits x
  have hIncFits' : (IntVal.num (↑(xNat x) + 1)).signedFits257 = true := by
    simpa using hIncFits
  dsimp [st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas,
    st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrArithInc
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.popInt
    , VM.pop
    , VM.pushIntQuiet
    , VM.push
    , IntVal.add
    , IntVal.inc
    , incFits
    , hIncFits'
    , gas_step4_nonneg
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]

private theorem execInstrToy_run_newc_st8Gas (x : Counter32) :
    (execInstrToy .newc).run (st8Gas x) = (.ok (), st9 x) := by
  dsimp [st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas,
    st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrCellNewc
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.push
    , gas_step7_nonneg
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]

private theorem execInstrToy_run_modPow2_st7Gas (x : Counter32) :
    (execInstrToy (.arithExt (.shrMod false false 2 (-1) false none))).run (st7Gas x) = (.ok (), st8 x) := by
  dsimp [st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load,
    st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrArithExt
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.checkUnderflow
    , VM.popNatUpTo
    , VM.popInt
    , VM.pop
    , VM.pushIntQuiet
    , VM.push
    , popNatUpToSigned
    , popGasRange
    , popGasRange
    , decRange
    , modFits
    , modPow2Fits'
    , modPow2Fits
    , rInt
    , gas_step6_nonneg
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]
  try rfl
  try rfl

private theorem builderEmpty_canExtendBy_32 : Builder.empty.canExtendBy 32 = true := by
  native_decide

private theorem execInstr_run_stu32_st9Gas (x : Counter32) :
    (execInstr stubHost (.stu 32)).run (st9Gas x) = (.ok (), st10 x) := by
  have hRange :
      ¬ ((((↑(xNat x) : Int) + 1) % 4294967296 < 0) ∨
        intPow2 32 ≤ (((↑(xNat x) : Int) + 1) % 4294967296)) := by
    exact (decide_eq_false_iff_not.mp (modExpr_decRange x))
  dsimp [st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4',
    st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstr_stu32
    , execInstrToy
    , execInstrCellStu
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.checkUnderflow
    , VM.popBuilder
    , VM.popInt
    , VM.pop
    , VM.push
    , builderEmpty_canExtendBy_32
    , hRange
    , modExpr_toNat
    , rInt_eq
    , VmState.consumeGas
    , GasLimits.consume
    , GasLimits.ofLimits
    , instrGas
    , gasPerInstr
    ]

private theorem execInstrToy_run_stu32_st9Gas (x : Counter32) :
    (execInstrToy (.stu 32)).run (st9Gas x) = (.ok (), st10 x) := by
  simpa [execInstr_stu32] using execInstr_run_stu32_st9Gas x

private theorem execInstrToy_run_endc_st10Gas (x : Counter32) :
    (execInstrToy .endc).run (st10Gas x) = (.ok (), st11 x) := by
  dsimp [st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6,
    st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1,
    st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrCellEndc
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.popBuilder
    , VM.pop
    , VM.push
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]
  simpa [outCell, encodeCounter]

private theorem execInstrToy_run_popCtr4_st11Gas (x : Counter32) :
    (execInstrToy (.popCtr 4)).run (st11Gas x) = (.ok (), st12 x) := by
  dsimp [st12, st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7,
    st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2,
    st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ execInstrToy
    , execInstrContPopCtr
    , vm_bind_run
    , vm_get_run
    , vm_pure_run
    , vm_throw_run
    , VM.popCell
    , VM.pop
    , VmState.setCtr
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]

private theorem step0_eval (x : Counter32) :
    (st1 x).step stubHost = StepResult.continue (st2 x) := by
  -- Precompute the out-of-gas checks so `simp` doesn't try to normalize huge integer expressions.
  have hGas0 : decide ((st1Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas,
      gasPerInstr] using gas_step0_nonneg
  have hGas1 : decide ((st2 x).gas.gasRemaining < 0) = false := by
    -- `PUSHCTR` only changes the stack.
    simpa [st2] using hGas0
  -- Make the `cc` scrutinee concrete before unfolding the (large) `VmState.step` definition.
  dsimp [st1, st0, VmState.initial]
  simp
    [ VmState.step
    , VmState.stepOrdinary
    , VmState.stepOrdinaryDecode
    , VmState.stepOrdinaryOk
    , applyCregsCdata_empty
    , bitsRemaining_ofCell_toyCounterCode
    , decode_ofCell_toyCounterCode
    , hGas0
    , execInstr_run_pushCtr4
    , hGas1
    ]
  try rfl

private theorem step1_eval (x : Counter32) :
    (st2 x).step stubHost = StepResult.continue (st3 x) := by
  dsimp [st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ VmState.step
    , VmState.stepOrdinary
    , VmState.stepOrdinaryDecode
    , VmState.stepOrdinaryOk
    , applyCregsCdata_empty
    , bitsRemaining_code1
    , decode_code1
    , execInstr_ctos
    , execInstrToy
    , execInstrCellCtos
    , encodeCounter_special
    , VM.registerCellLoad
    , VmState.registerCellLoad
    , VM.popCell
    , VM.pop
    , VM.push
    , gas_step1_nonneg
    , gas_step1_post_nonneg
    , registerCellLoad_gasRemaining
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]
  try rfl
  try rfl
  try rfl

private theorem step2_eval (x : Counter32) :
    (st3 x).step stubHost = StepResult.continue (st4 x) := by
  dsimp [st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ VmState.step
    , VmState.stepOrdinary
    , VmState.stepOrdinaryDecode
    , VmState.stepOrdinaryOk
    , applyCregsCdata_empty
    , bitsRemaining_code2
    , decode_code2
    , execInstr_ldu32
    , execInstrToy
    , execInstrCellLdu
    , vm_bind_run
    , vm_get_run
    , vm_modify_run
    , vm_pure_run
    , vm_throw_run
    , VM.popSlice
    , VM.pop
    , VM.push
    , Except.map
    , Array.back_eq_getElem
    , inputSlice_haveBits_32
    , xNat
    , registerCellLoad_cc
    , registerCellLoad_cp
    , VmState.registerCellLoad
    , registerCellLoad_gasRemaining
    , gas_step2_nonneg
    , VmState.consumeGas
    , GasLimits.consume
    , GasLimits.ofLimits
    , instrGas
    , gasPerInstr
    ]
  try rfl
  try rfl
  try rfl

private theorem step3_eval (x : Counter32) :
    (st4 x).step stubHost = StepResult.continue (st5 x) := by
  have hGas0 : decide ((st4Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0,
      VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr,
      registerCellLoad_gasRemaining] using gas_step3_nonneg
  have hGas1 : decide ((st5 x).gas.gasRemaining < 0) = false := by
    simpa [st5] using hGas0
  rw [VmState.step, st4_cc]
  change VmState.stepOrdinary stubHost (st4 x) code3 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st5 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code3]
  change VmState.stepOrdinaryDecode stubHost (st4 x) code3 = StepResult.continue (st5 x)
  simp [VmState.stepOrdinaryDecode, st4_cp, decode_code3]
  change VmState.stepOrdinaryOk stubHost (st4 x) (.pop 0) 8 code4 = StepResult.continue (st5 x)
  let st4cc0 : VmState := { (st4 x) with cc := .ordinary code4 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st4cc0.consumeGas (instrGas (.pop 0) 8)).gas.gasRemaining < 0) = false := by
    simpa [st4cc0, st4Gas, st4', st4_cp] using hGas0
  have hRun0 : (execInstrToy (.pop 0)).run (st4cc0.consumeGas (instrGas (.pop 0) 8)) = (.ok (), st5 x) := by
    simpa [st4cc0, st4Gas, st4', st4_cp] using execInstrToy_run_pop0_st4Gas x
  simp [VmState.stepOrdinaryOk, st4cc0, st4_cp, hGas0', hRun0, hGas1]

private theorem step4_eval (x : Counter32) :
    (st5 x).step stubHost = StepResult.continue (st6 x) := by
  have hGas0 : decide ((st5Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas,
      st1', st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr,
      registerCellLoad_gasRemaining] using gas_step4_nonneg
  have hGas1 : decide ((st6 x).gas.gasRemaining < 0) = false := by
    simpa [st6] using hGas0
  rw [VmState.step, st5_cc]
  change VmState.stepOrdinary stubHost (st5 x) code4 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st6 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code4]
  change VmState.stepOrdinaryDecode stubHost (st5 x) code4 = StepResult.continue (st6 x)
  simp [VmState.stepOrdinaryDecode, st5_cp, decode_code4]
  change VmState.stepOrdinaryOk stubHost (st5 x) .inc 8 code5 = StepResult.continue (st6 x)
  let st5cc0 : VmState := { (st5 x) with cc := .ordinary code5 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st5cc0.consumeGas (instrGas .inc 8)).gas.gasRemaining < 0) = false := by
    simpa [st5cc0, st5Gas, st5', st5_cp] using hGas0
  have hRun0 : (execInstrToy .inc).run (st5cc0.consumeGas (instrGas .inc 8)) = (.ok (), st6 x) := by
    simpa [st5cc0, st5Gas, st5', st5_cp] using execInstrToy_run_inc_st5Gas x
  simp [VmState.stepOrdinaryOk, st5cc0, st5_cp, hGas0', hRun0, hGas1]

private theorem step5_eval (x : Counter32) :
    (st6 x).step stubHost = StepResult.continue (st7 x) := by
  dsimp [st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas,
    st2', st2, st1Gas, st1', st1, st0, VmState.initial]
  simp (config := { contextual := false })
    [ VmState.step
    , VmState.stepOrdinary
    , VmState.stepOrdinaryDecode
    , VmState.stepOrdinaryOk
    , applyCregsCdata_empty
    , bitsRemaining_code5
    , decode_code5
    , execInstr_pushInt32
    , execInstrToy
    , execInstrStackPushInt
    , VM.pushIntQuiet
    , signedFits257_num32
    , VM.push
    , gas_step5_nonneg
    , VmState.consumeGas
    , GasLimits.consume
    , instrGas
    , gasPerInstr
    , GasLimits.ofLimits
    ]
  try rfl

private theorem step6_eval (x : Counter32) :
    (st7 x).step stubHost = StepResult.continue (st8 x) := by
  have hGas0 : decide ((st7Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load,
      st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume,
      GasLimits.ofLimits, instrGas, gasPerInstr, registerCellLoad_gasRemaining] using gas_step6_nonneg
  have hGas1 : decide ((st8 x).gas.gasRemaining < 0) = false := by
    simpa [st8] using hGas0
  rw [VmState.step, st7_cc]
  change VmState.stepOrdinary stubHost (st7 x) code6 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st8 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code6]
  change VmState.stepOrdinaryDecode stubHost (st7 x) code6 = StepResult.continue (st8 x)
  simp [VmState.stepOrdinaryDecode, st7_cp, decode_code6]
  change VmState.stepOrdinaryOk stubHost (st7 x) (.arithExt (.shrMod false false 2 (-1) false none)) 16 code7 =
      StepResult.continue (st8 x)
  let st7cc0 : VmState := { (st7 x) with cc := .ordinary code7 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' :
      decide ((st7cc0.consumeGas (instrGas (.arithExt (.shrMod false false 2 (-1) false none)) 16)).gas.gasRemaining < 0) =
        false := by
    simpa [st7cc0, st7Gas, st7', st7_cp] using hGas0
  have hRun0 :
      (execInstrToy (.arithExt (.shrMod false false 2 (-1) false none))).run
          (st7cc0.consumeGas (instrGas (.arithExt (.shrMod false false 2 (-1) false none)) 16)) =
        (.ok (), st8 x) := by
    simpa [st7cc0, st7Gas, st7', st7_cp] using execInstrToy_run_modPow2_st7Gas x
  simp [VmState.stepOrdinaryOk, st7cc0, st7_cp, hGas0', hRun0, hGas1]

private theorem step7_eval (x : Counter32) :
    (st8 x).step stubHost = StepResult.continue (st9 x) := by
  have hGas0 : decide ((st8Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas,
      st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas,
      GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr, registerCellLoad_gasRemaining] using gas_step7_nonneg
  have hGas1 : decide ((st9 x).gas.gasRemaining < 0) = false := by
    simpa [st9] using hGas0
  rw [VmState.step, st8_cc]
  change VmState.stepOrdinary stubHost (st8 x) code7 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st9 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code7]
  change VmState.stepOrdinaryDecode stubHost (st8 x) code7 = StepResult.continue (st9 x)
  simp [VmState.stepOrdinaryDecode, st8_cp, decode_code7]
  change VmState.stepOrdinaryOk stubHost (st8 x) .newc 8 code8 = StepResult.continue (st9 x)
  let st8cc0 : VmState := { (st8 x) with cc := .ordinary code8 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st8cc0.consumeGas (instrGas .newc 8)).gas.gasRemaining < 0) = false := by
    simpa [st8cc0, st8Gas, st8', st8_cp] using hGas0
  have hRun0 : (execInstrToy .newc).run (st8cc0.consumeGas (instrGas .newc 8)) = (.ok (), st9 x) := by
    simpa [st8cc0, st8Gas, st8', st8_cp] using execInstrToy_run_newc_st8Gas x
  simp [VmState.stepOrdinaryOk, st8cc0, st8_cp, hGas0', hRun0, hGas1]

private theorem step8_eval (x : Counter32) :
    (st9 x).step stubHost = StepResult.continue (st10 x) := by
  have hGas0 : decide ((st9Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4,
      st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas,
      GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr, registerCellLoad_gasRemaining] using gas_step8_nonneg
  have hGas1 : decide ((st10 x).gas.gasRemaining < 0) = false := by
    simpa [st10] using hGas0
  rw [VmState.step, st9_cc]
  change VmState.stepOrdinary stubHost (st9 x) code8 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st10 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code8]
  change VmState.stepOrdinaryDecode stubHost (st9 x) code8 = StepResult.continue (st10 x)
  simp [VmState.stepOrdinaryDecode, st9_cp, decode_code8]
  change VmState.stepOrdinaryOk stubHost (st9 x) (.stu 32) 16 code9 = StepResult.continue (st10 x)
  let st9cc0 : VmState := { (st9 x) with cc := .ordinary code9 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st9cc0.consumeGas (instrGas (.stu 32) 16)).gas.gasRemaining < 0) = false := by
    simpa [st9cc0, st9Gas, st9', st9_cp] using hGas0
  have hRun0 : (execInstrToy (.stu 32)).run (st9cc0.consumeGas (instrGas (.stu 32) 16)) = (.ok (), st10 x) := by
    simpa [st9cc0, st9Gas, st9', st9_cp] using execInstrToy_run_stu32_st9Gas x
  simp [VmState.stepOrdinaryOk, st9cc0, st9_cp, hGas0', hRun0, hGas1]

private theorem step9_eval (x : Counter32) :
    (st10 x).step stubHost = StepResult.continue (st11 x) := by
  have hGas0 : decide ((st10Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5',
      st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0,
      VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr,
      registerCellLoad_gasRemaining] using gas_step9_nonneg
  have hGas1 : decide ((st11 x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7, st6Gas, st6', st6,
      st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1',
      st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr,
      registerCellLoad_gasRemaining] using gas_step9_post_nonneg
  rw [VmState.step, st10_cc]
  change VmState.stepOrdinary stubHost (st10 x) code9 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st11 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code9]
  change VmState.stepOrdinaryDecode stubHost (st10 x) code9 = StepResult.continue (st11 x)
  simp [VmState.stepOrdinaryDecode, st10_cp, decode_code9]
  change VmState.stepOrdinaryOk stubHost (st10 x) .endc 8 code10 = StepResult.continue (st11 x)
  let st10cc0 : VmState := { (st10 x) with cc := .ordinary code10 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st10cc0.consumeGas (instrGas .endc 8)).gas.gasRemaining < 0) = false := by
    simpa [st10cc0, st10Gas, st10', st10_cp] using hGas0
  have hRun0 : (execInstrToy .endc).run (st10cc0.consumeGas (instrGas .endc 8)) = (.ok (), st11 x) := by
    simpa [st10cc0, st10Gas, st10', st10_cp] using execInstrToy_run_endc_st10Gas x
  simp [VmState.stepOrdinaryOk, st10cc0, st10_cp, hGas0', hRun0, hGas1]

private theorem step10_eval (x : Counter32) :
    (st11 x).step stubHost = StepResult.continue (st12 x) := by
  have hGas0 : decide ((st11Gas x).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7', st7,
      st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2', st2,
      st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas, gasPerInstr,
      registerCellLoad_gasRemaining] using gas_step10_nonneg
  have hGas1 : decide ((st12 x).gas.gasRemaining < 0) = false := by
    simpa [st12] using hGas0
  rw [VmState.step, st11_cc]
  change VmState.stepOrdinary stubHost (st11 x) code10 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st12 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code10]
  change VmState.stepOrdinaryDecode stubHost (st11 x) code10 = StepResult.continue (st12 x)
  simp [VmState.stepOrdinaryDecode, st11_cp, decode_code10]
  change VmState.stepOrdinaryOk stubHost (st11 x) (.popCtr 4) 16 code11 = StepResult.continue (st12 x)
  let st11cc0 : VmState := { (st11 x) with cc := .ordinary code11 (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0 }
  have hGas0' : decide ((st11cc0.consumeGas (instrGas (.popCtr 4) 16)).gas.gasRemaining < 0) = false := by
    simpa [st11cc0, st11Gas, st11', st11_cp] using hGas0
  have hRun0 : (execInstrToy (.popCtr 4)).run (st11cc0.consumeGas (instrGas (.popCtr 4) 16)) = (.ok (), st12 x) := by
    simpa [st11cc0, st11Gas, st11', st11_cp] using execInstrToy_run_popCtr4_st11Gas x
  simp [VmState.stepOrdinaryOk, st11cc0, st11_cp, hGas0', hRun0, hGas1]

@[simp] private theorem st12_regs_c0 (x : Counter32) :
    (st12 x).regs.c0 = .quit 0 := by
  simp [st12, st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas,
    st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop,
    st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas, Regs.initial]

@[simp] private theorem st12_gasRemaining (x : Counter32) :
    (st12 x).gas.gasRemaining =
      GasLimits.infty - 26 - 18 - cellLoadGasPrice - 26 - 18 - 18 - 26 - 26 - 18 - 26 - 18 - cellCreateGasPrice - 26 := by
  simp [st12, st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7',
    st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas,
    st2', st2, st1Gas, st1', st1, st0, VmState.initial, VmState.consumeGas, GasLimits.consume, GasLimits.ofLimits, instrGas,
    gasPerInstr, registerCellLoad_gasRemaining]

private theorem vm_ret_run_st12ConsumeGas (x : Counter32) :
    (VM.ret).run ((st12 x).consumeGas implicitRetGasPrice) = (.ok (), st13 x) := by
  simp [VM.ret, VM.jump, vm_bind_run, vm_get_run, vm_set_run, vm_modify_run, vm_pure_run, vm_throw_run, st13,
    st12_regs_c0]

private theorem step11_eval (x : Counter32) :
    (st12 x).step stubHost = StepResult.continue (st13 x) := by
  have hGas : decide (((st12 x).consumeGas implicitRetGasPrice).gas.gasRemaining < 0) = false := by
    apply decide_eq_false
    simpa [st12_gasRemaining x, VmState.consumeGas, GasLimits.consume] using gas_step11_nonneg
  rw [VmState.step, st12_cc]
  change VmState.stepOrdinary stubHost (st12 x) code11 (.quit 0) OrdCregs.empty OrdCdata.empty =
      StepResult.continue (st13 x)
  simp [VmState.stepOrdinary, applyCregsCdata_empty, bitsRemaining_code11]
  change VmState.stepOrdinaryImplicit (st12 x) code11 = StepResult.continue (st13 x)
  simp [VmState.stepOrdinaryImplicit, refsRemaining_code11, hGas, vm_ret_run_st12ConsumeGas x]

private theorem step12_eval (x : Counter32) :
    (st13 x).step stubHost = StepResult.halt (-1) (st13 x) := by
  rfl

-- `Cell.depthLe` only depends on the cell graph. For cells with no references, any positive
-- depth limit succeeds immediately.
private theorem cell_depthLe_succ_of_refs_empty (c : Cell) (limit : Nat) (h : c.refs = #[]) :
    c.depthLe (Nat.succ limit) = true := by
  -- `Array.all` on an empty reference array is `true`.
  simp [Cell.depthLe, h]

@[simp] private theorem st13_maxDataDepth (x : Counter32) :
    (st13 x).maxDataDepth = 512 := by
  simp [st13, st12, st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8,
    st7Gas, st7', st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3,
    st2Load, st2Pop, st2Gas, st2', st2, st1Gas, st1', st1, st0, VmState.initial, consumeGas_maxDataDepth,
    registerCellLoad_maxDataDepth]

@[simp] private theorem st13_regs_c4 (x : Counter32) :
    (st13 x).regs.c4 = outCell x := by
  simp [st13, st12, VmState.consumeGas]

@[simp] private theorem st13_regs_c5 (x : Counter32) :
    (st13 x).regs.c5 = Cell.empty := by
  simp [st13, st12, st11Gas, st11', st11, st10Gas2, st10Gas, st10', st10, st9Gas, st9', st9, st8Gas, st8', st8, st7Gas, st7',
    st7, st6Gas, st6', st6, st5Gas, st5', st5, st4Gas, st4', st4, st3Pop, st3Gas, st3', st3, st2Load, st2Pop, st2Gas, st2',
    st2, st1Gas, st1', st1, st0, VmState.initial, Regs.initial]

private theorem st13_c4_depthLe (x : Counter32) :
    (st13 x).regs.c4.depthLe (st13 x).maxDataDepth = true := by
  have hrefs : (outCell x).refs = #[] := by
    simp [outCell, encodeCounter_refs]
  have hc4' : (st13 x).regs.c4.depthLe 512 = true := by
    simpa using cell_depthLe_succ_of_refs_empty (c := outCell x) (limit := 511) hrefs
  simpa using hc4'

private theorem st13_c5_depthLe (x : Counter32) :
    (st13 x).regs.c5.depthLe (st13 x).maxDataDepth = true := by
  have hrefs : Cell.empty.refs = #[] := by rfl
  have hc5' : (st13 x).regs.c5.depthLe 512 = true := by
    simpa using cell_depthLe_succ_of_refs_empty (c := Cell.empty) (limit := 511) hrefs
  simpa using hc5'

private theorem st13_tryCommit_ok (x : Counter32) :
    (st13 x).tryCommit.fst = true := by
  have hc4_512 : (outCell x).depthLe 512 = true := by
    have hrefs : (outCell x).refs = #[] := by
      simp [outCell, encodeCounter_refs]
    simpa using cell_depthLe_succ_of_refs_empty (c := outCell x) (limit := 511) hrefs
  have hc5_512 : Cell.empty.depthLe 512 = true := by
    have hrefs : Cell.empty.refs = #[] := by
      rfl
    simpa using cell_depthLe_succ_of_refs_empty (c := Cell.empty) (limit := 511) hrefs
  have hCond : (outCell x).depthLe 512 = true ∧ Cell.empty.depthLe 512 = true := by
    exact ⟨hc4_512, hc5_512⟩
  unfold VmState.tryCommit
  simp [hCond]

private theorem runToyCounter_script (x : Counter32) (fuelTail : Nat) :
    RunScript stubHost (fuelTail + 13) (st1 x) (Sum.inl (-1, st13 x)) := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (by
    vm_script [
      step0_eval x,
      step1_eval x,
      step2_eval x,
      step3_eval x,
      step4_eval x,
      step5_eval x,
      step6_eval x,
      step7_eval x,
      step8_eval x,
      step9_eval x,
      step10_eval x,
      step11_eval x,
      step12_eval x
    ])

private theorem runToyCounter_runRaw_halt_withFuel (x : Counter32) (fuelTail : Nat) :
    VmState.runRaw stubHost (fuelTail + 13) (st1 x) = StepResult.halt (-1) (st13 x) := by
  simpa using
    runRaw_of_script_halt (host := stubHost) (fuel := fuelTail + 13) (st := st1 x) (st' := st13 x)
      (exitCode := -1) (runToyCounter_script x fuelTail)

private theorem runToyCounter_halt_withFuel (x : Counter32) (fuelTail : Nat) :
    VmState.run stubHost (fuelTail + 13) (st1 x) = StepResult.halt (-1) ((st13 x).tryCommit).2 := by
  have hrun :
      VmState.run stubHost (fuelTail + 13) (st1 x) = VmState.finalizeHalt (-1) (st13 x) := by
    simpa using
      run_of_script_halt (host := stubHost) (fuel := fuelTail + 13) (st := st1 x) (st' := st13 x)
        (exitCode := -1) (runToyCounter_script x fuelTail)
  have hok : (st13 x).tryCommit.fst = true := st13_tryCommit_ok x
  rw [hrun]
  simpa using
    (VmState.finalizeHalt_commit_ok (st := st13 x) (exitCode := (-1)) (hexit := by simp) hok)

private theorem runToyCounter_halt (x : Counter32) :
    VmState.run stubHost 50 (st1 x) = StepResult.halt (-1) ((st13 x).tryCommit).2 := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using runToyCounter_halt_withFuel x 37

private theorem runToyCounter_halt_133 (x : Counter32) :
    VmState.run stubHost 133 (st1 x) = StepResult.halt (-1) ((st13 x).tryCommit).2 := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using runToyCounter_halt_withFuel x 120

private theorem runToyCounter_eval_outCell (x : Counter32) :
    runToyCounter (init x) = .ok { c4 := outCell x } := by
  have hRunRaw : VmState.runRaw stubHost 50 (st1 x) = StepResult.halt (-1) (st13 x) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using runToyCounter_runRaw_halt_withFuel x 37
  have hok : (st13 x).tryCommit.fst = true := st13_tryCommit_ok x
  have hRun :
      VmState.finalizeRunResult (VmState.runRaw stubHost 50 (st1 x)) =
        StepResult.halt (-1) ((st13 x).tryCommit).2 := by
    rw [hRunRaw]
    unfold VmState.finalizeRunResult
    simpa using
      (VmState.finalizeHalt_commit_ok (st := st13 x) (exitCode := (-1)) (hexit := by simp) hok)
  have hc4_commit : ((st13 x).tryCommit).2.regs.c4 = outCell x := by
    simpa [tryCommit_regs] using (st13_regs_c4 x)
  change
    extractCounterState (VmState.finalizeRunResult (VmState.runRaw stubHost 50 (st1 x))) =
      Except.ok ({ c4 := outCell x } : CounterState)
  rw [hRun]
  have hexit : ((-1 : Int) = -1 ∨ (-1 : Int) = -2) := by
    simp
  simp [extractCounterState, hexit, hc4_commit]

private theorem outCell_eq_expected (x : Counter32) :
    outCell x = encodeCounter ((encodedInputValue x + 1) % (2 ^ 32)) := by
  have hxNat : xNat x = encodedInputValue x := xNat_eq_encodedInputValue x
  have hpow32 : (2 ^ 32 : Nat) = 4294967296 := by native_decide
  calc
    outCell x = encodeCounter (((Int.ofNat (xNat x) + 1) % 4294967296).toNat) := by rfl
    _ = encodeCounter ((xNat x + 1) % 4294967296) := by
      exact congrArg encodeCounter (modExpr_toNat x)
    _ = encodeCounter ((encodedInputValue x + 1) % 4294967296) := by simp [hxNat]
    _ = encodeCounter ((encodedInputValue x + 1) % (2 ^ 32)) := by simpa [hpow32]

theorem runToyCounter_eval (x : Counter32) :
    runToyCounter (init x) = .ok { c4 := encodeCounter ((encodedInputValue x + 1) % (2 ^ 32)) } := by
  simpa [outCell_eq_expected x] using runToyCounter_eval_outCell x

theorem tvm_matches_spec (x : Counter32) :
    runToyCounter (init x) = runToyContract (init x) := by
  simp [runToyCounter_eval, runToyContract_eval]

end Proofs.ToyCounter
