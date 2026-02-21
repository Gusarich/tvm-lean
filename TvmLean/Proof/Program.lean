import TvmLean.Proof.Gas

namespace TvmLean

def StepResult.exitCode? : StepResult → Option Int
  | .continue _ => none
  | .halt exitCode _ => some exitCode

def StepResult.state : StepResult → VmState
  | .continue st => st
  | .halt _ st => st

def StepResult.finalC4 (res : StepResult) : Cell :=
  res.state.regs.c4

def StepResult.finalStack (res : StepResult) : Stack :=
  res.state.stack

def StepResult.finalRegs (res : StepResult) : Regs :=
  res.state.regs

def StepResult.finalGasRemaining (res : StepResult) : Int :=
  res.state.gas.gasRemaining

def StepResult.isContinue : StepResult → Bool
  | .continue _ => true
  | .halt _ _ => false

def StepResult.isHalt : StepResult → Bool
  | .continue _ => false
  | .halt _ _ => true

@[simp] theorem stepResult_exitCode?_continue (st : VmState) :
    (StepResult.continue st).exitCode? = none := by
  rfl

@[simp] theorem stepResult_exitCode?_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).exitCode? = some exitCode := by
  rfl

@[simp] theorem stepResult_state_continue (st : VmState) :
    (StepResult.continue st).state = st := by
  rfl

@[simp] theorem stepResult_state_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).state = st := by
  rfl

@[simp] theorem stepResult_finalStack_continue (st : VmState) :
    (StepResult.continue st).finalStack = st.stack := by
  rfl

@[simp] theorem stepResult_finalStack_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).finalStack = st.stack := by
  rfl

@[simp] theorem stepResult_finalRegs_continue (st : VmState) :
    (StepResult.continue st).finalRegs = st.regs := by
  rfl

@[simp] theorem stepResult_finalRegs_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).finalRegs = st.regs := by
  rfl

@[simp] theorem stepResult_finalGasRemaining_continue (st : VmState) :
    (StepResult.continue st).finalGasRemaining = st.gas.gasRemaining := by
  rfl

@[simp] theorem stepResult_finalGasRemaining_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).finalGasRemaining = st.gas.gasRemaining := by
  rfl

@[simp] theorem stepResult_isContinue_continue (st : VmState) :
    (StepResult.continue st).isContinue = true := by
  rfl

@[simp] theorem stepResult_isContinue_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).isContinue = false := by
  rfl

@[simp] theorem stepResult_isHalt_continue (st : VmState) :
    (StepResult.continue st).isHalt = false := by
  rfl

@[simp] theorem stepResult_isHalt_halt (exitCode : Int) (st : VmState) :
    (StepResult.halt exitCode st).isHalt = true := by
  rfl

@[simp] theorem VmState.execProgram_nil (host : Host) (st : VmState) :
    VmState.execProgram host [] st = .continue st := by
  rfl

@[simp] theorem VmState.execProgram_cons (host : Host) (instr : Instr) (rest : List Instr) (st : VmState) :
    VmState.execProgram host (instr :: rest) st =
      match VmState.execProgramStep host instr st with
      | .halt exitCode st' => .halt exitCode st'
      | .continue st' => VmState.execProgram host rest st' := by
  rfl

@[simp] theorem VmState.execProgram_single (host : Host) (instr : Instr) (st : VmState) :
    VmState.execProgram host [instr] st = VmState.execProgramStep host instr st := by
  cases hstep : VmState.execProgramStep host instr st <;> simp [VmState.execProgram, hstep]

theorem VmState.execProgramStep_unfold (host : Host) (instr : Instr) (st : VmState) :
    VmState.execProgramStep host instr st =
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
                .continue stExcGas := by
  rfl

theorem VmState.execProgram_cons_continue (host : Host) (instr : Instr) (rest : List Instr) (st st' : VmState)
    (hstep : VmState.execProgramStep host instr st = .continue st') :
    VmState.execProgram host (instr :: rest) st = VmState.execProgram host rest st' := by
  simp [VmState.execProgram, hstep]

theorem VmState.execProgram_cons_halt (host : Host) (instr : Instr) (rest : List Instr)
    (st st' : VmState) (exitCode : Int)
    (hstep : VmState.execProgramStep host instr st = .halt exitCode st') :
    VmState.execProgram host (instr :: rest) st = .halt exitCode st' := by
  simp [VmState.execProgram, hstep]

theorem VmState.execProgram_precheck_false_ofProgram
    (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram program).sufficientFor st) :
    decide (st.gas.gasRemaining < programBaseGas program) = false := by
  exact GasBudget.ofProgram_check_false (program := program) (st := st) hsufficient

theorem VmState.execProgram_guard_ofProgram
    (host : Host) (program : List Instr) (st : VmState)
    (hsufficient : (GasBudget.ofProgram program).sufficientFor st) :
    (if decide (st.gas.gasRemaining < programBaseGas program) then
      st.outOfGasHalt
    else
      VmState.execProgram host program st) = VmState.execProgram host program st := by
  have hpre :
      decide (st.gas.gasRemaining < programBaseGas program) = false :=
    VmState.execProgram_precheck_false_ofProgram
      (program := program)
      (st := st)
      hsufficient
  simp [hpre]

def decodeCp0AllAux : Nat → Slice → Except Excno (List Instr × Slice)
  | 0, code =>
      .ok ([], code)
  | fuel + 1, code =>
      if code.bitsRemaining == 0 then
        .ok ([], code)
      else
        match decodeCp0WithBits code with
        | .ok (instr, _totBits, rest) =>
            match decodeCp0AllAux fuel rest with
            | .ok (tail, rest') => .ok (instr :: tail, rest')
            | .error e => .error e
        | .error e => .error e

def decodeCp0All (fuel : Nat) (code : Slice) : Except Excno (List Instr) := do
  let (program, rest) ← decodeCp0AllAux fuel code
  if (rest.bitsRemaining == 0) && (rest.refsRemaining == 0) then
    return program
  else
    throw .invOpcode

def decodeCp0AllFromCell (fuel : Nat) (code : Cell) : Except Excno (List Instr) :=
  decodeCp0All fuel (Slice.ofCell code)

def VmState.execDecodedCp0 (host : Host) (fuel : Nat) (code : Cell) (st : VmState) :
    Except Excno StepResult := do
  let program ← decodeCp0AllFromCell fuel code
  return VmState.execProgram host program st

def assembleAndDecodeCp0 (fuel : Nat) (program : List Instr) : Except Excno (List Instr) := do
  let code ← assembleCp0 program
  decodeCp0AllFromCell fuel code

def assembleDecodeMatches (fuel : Nat) (program : List Instr) : Bool :=
  match assembleAndDecodeCp0 fuel program with
  | .ok decoded => decoded == program
  | .error _ => false

@[simp] theorem decodeCp0AllAux_zero (code : Slice) :
    decodeCp0AllAux 0 code = .ok ([], code) := by
  rfl

@[simp] theorem decodeCp0AllAux_stop (fuel : Nat) (code : Slice)
    (hbits : code.bitsRemaining == 0) :
    decodeCp0AllAux (fuel + 1) code = .ok ([], code) := by
  simp [decodeCp0AllAux, hbits]

theorem decodeCp0AllAux_succ_decode_ok (fuel : Nat) (code rest : Slice) (instr : Instr) (totBits : Nat)
    (hbits : (code.bitsRemaining == 0) = false)
    (hdecode : decodeCp0WithBits code = .ok (instr, totBits, rest)) :
    decodeCp0AllAux (fuel + 1) code =
      match decodeCp0AllAux fuel rest with
      | .ok (tail, rest') => .ok (instr :: tail, rest')
      | .error e => .error e := by
  simp [decodeCp0AllAux, hbits, hdecode]

theorem decodeCp0AllAux_succ_decode_error (fuel : Nat) (code : Slice) (e : Excno)
    (hbits : (code.bitsRemaining == 0) = false)
    (hdecode : decodeCp0WithBits code = .error e) :
    decodeCp0AllAux (fuel + 1) code = .error e := by
  simp [decodeCp0AllAux, hbits, hdecode]

theorem decodeCp0All_ok_of_aux_ok_remainder_empty
    (fuel : Nat) (code : Slice) (program : List Instr) (rest : Slice)
    (haux : decodeCp0AllAux fuel code = .ok (program, rest))
    (hbits : rest.bitsRemaining = 0)
    (hrefs : rest.refsRemaining = 0) :
    decodeCp0All fuel code = .ok program := by
  have hform :
      decodeCp0All fuel code =
        (if ((rest.bitsRemaining == 0) && (rest.refsRemaining == 0)) = true
          then (Except.ok program : Except Excno (List Instr))
          else (Except.error Excno.invOpcode : Except Excno (List Instr))) := by
    unfold decodeCp0All
    rw [haux]
    rfl
  rw [hform]
  simp [hbits, hrefs]

theorem decodeCp0All_aux_ok_remainder_empty_of_ok
    (fuel : Nat) (code : Slice) (program : List Instr)
    (hok : decodeCp0All fuel code = .ok program) :
    ∃ rest, decodeCp0AllAux fuel code = .ok (program, rest) ∧
      rest.bitsRemaining = 0 ∧ rest.refsRemaining = 0 := by
  cases haux : decodeCp0AllAux fuel code with
  | error e =>
      have hform : decodeCp0All fuel code = (Except.error e : Except Excno (List Instr)) := by
        unfold decodeCp0All
        rw [haux]
        rfl
      rw [hform] at hok
      cases hok
  | ok pair =>
      rcases pair with ⟨program', rest⟩
      have hform :
          decodeCp0All fuel code =
            (if ((rest.bitsRemaining == 0) && (rest.refsRemaining == 0)) = true
              then (Except.ok program' : Except Excno (List Instr))
              else (Except.error Excno.invOpcode : Except Excno (List Instr))) := by
        unfold decodeCp0All
        rw [haux]
        rfl
      rw [hform] at hok
      by_cases hrem : ((rest.bitsRemaining == 0) && (rest.refsRemaining == 0)) = true
      · have hprog : program' = program := by
          simp [hrem] at hok
          exact hok
        have hparts : (rest.bitsRemaining == 0) = true ∧ (rest.refsRemaining == 0) = true := by
          simpa [Bool.and_eq_true] using hrem
        have hbits : rest.bitsRemaining = 0 := by
          simpa [Nat.beq_eq_true_eq] using hparts.1
        have hrefs : rest.refsRemaining = 0 := by
          simpa [Nat.beq_eq_true_eq] using hparts.2
        refine ⟨rest, ?_, hbits, hrefs⟩
        simpa [hprog] using haux
      · simp [hrem] at hok

theorem decodeCp0All_ok_iff_aux_ok_remainder_empty
    (fuel : Nat) (code : Slice) (program : List Instr) :
    decodeCp0All fuel code = .ok program ↔
      ∃ rest, decodeCp0AllAux fuel code = .ok (program, rest) ∧
        rest.bitsRemaining = 0 ∧ rest.refsRemaining = 0 := by
  constructor
  · intro hok
    exact decodeCp0All_aux_ok_remainder_empty_of_ok
      (fuel := fuel) (code := code) (program := program) hok
  · intro h
    rcases h with ⟨rest, haux, hbits, hrefs⟩
    exact decodeCp0All_ok_of_aux_ok_remainder_empty
      (fuel := fuel) (code := code) (program := program) (rest := rest)
      haux hbits hrefs

theorem decodeCp0AllAux_succ_ok_of_ok_remainder_empty_bits
    (fuel : Nat) (code : Slice) (program : List Instr) (rest : Slice)
    (haux : decodeCp0AllAux fuel code = .ok (program, rest))
    (hrestBits : rest.bitsRemaining = 0) :
    decodeCp0AllAux (fuel + 1) code = .ok (program, rest) := by
  induction fuel generalizing code program rest with
  | zero =>
      have haux' : (.ok ([], code) : Except Excno (List Instr × Slice)) = .ok (program, rest) := by
        simpa [decodeCp0AllAux] using haux
      cases haux'
      have hstop : decodeCp0AllAux (0 + 1) code = .ok ([], code) :=
        decodeCp0AllAux_stop (fuel := 0) (code := code) ((beq_iff_eq).2 hrestBits)
      simpa using hstop
  | succ fuel ih =>
      by_cases hcodeBits : (code.bitsRemaining == 0) = true
      · have haux' : (.ok ([], code) : Except Excno (List Instr × Slice)) = .ok (program, rest) := by
          simpa [decodeCp0AllAux, hcodeBits] using haux
        cases haux'
        have hstop : decodeCp0AllAux ((fuel + 1) + 1) code = .ok ([], code) :=
          decodeCp0AllAux_stop (fuel := fuel + 1) (code := code) hcodeBits
        simpa using hstop
      · cases hdecode : decodeCp0WithBits code with
        | error e =>
            have hcodeBitsFalse : (code.bitsRemaining == 0) = false := (Bool.eq_false_iff).2 hcodeBits
            simp [decodeCp0AllAux, hcodeBitsFalse, hdecode] at haux
        | ok decoded =>
            rcases decoded with ⟨instr, totBits, nextCode⟩
            cases htail : decodeCp0AllAux fuel nextCode with
            | error e =>
                have hcodeBitsFalse : (code.bitsRemaining == 0) = false := (Bool.eq_false_iff).2 hcodeBits
                simp [decodeCp0AllAux, hcodeBitsFalse, hdecode, htail] at haux
            | ok tailPair =>
                rcases tailPair with ⟨tail, rest'⟩
                have hcodeBitsFalse : (code.bitsRemaining == 0) = false := (Bool.eq_false_iff).2 hcodeBits
                have hauxOk :
                    (.ok (instr :: tail, rest') : Except Excno (List Instr × Slice)) = .ok (program, rest) := by
                  simpa [decodeCp0AllAux, hcodeBitsFalse, hdecode, htail] using haux
                cases hauxOk
                have htailSucc :
                    decodeCp0AllAux (fuel + 1) nextCode = .ok (tail, rest) :=
                  ih (code := nextCode) (program := tail) (rest := rest) htail hrestBits
                have hstep :
                    decodeCp0AllAux ((fuel + 1) + 1) code =
                      match decodeCp0AllAux (fuel + 1) nextCode with
                      | .ok (tail'', rest'') => .ok (instr :: tail'', rest'')
                      | .error e => .error e :=
                  decodeCp0AllAux_succ_decode_ok
                    (fuel := fuel + 1) (code := code) (rest := nextCode)
                    (instr := instr) (totBits := totBits) (hbits := hcodeBitsFalse) (hdecode := hdecode)
                rw [hstep, htailSucc]

theorem decodeCp0AllAux_ok_mono_fuel_of_remainder_empty_bits
    (fuel extra : Nat) (code : Slice) (program : List Instr) (rest : Slice)
    (haux : decodeCp0AllAux fuel code = .ok (program, rest))
    (hrestBits : rest.bitsRemaining = 0) :
    decodeCp0AllAux (fuel + extra) code = .ok (program, rest) := by
  induction extra with
  | zero =>
      simpa using haux
  | succ extra ih =>
      have hs :
          decodeCp0AllAux ((fuel + extra) + 1) code = .ok (program, rest) :=
        decodeCp0AllAux_succ_ok_of_ok_remainder_empty_bits
          (fuel := fuel + extra) (code := code) (program := program) (rest := rest)
          (haux := ih) (hrestBits := hrestBits)
      simpa [Nat.add_assoc] using hs

theorem decodeCp0All_ok_mono_fuel
    (fuel extra : Nat) (code : Slice) (program : List Instr)
    (hok : decodeCp0All fuel code = .ok program) :
    decodeCp0All (fuel + extra) code = .ok program := by
  rcases decodeCp0All_aux_ok_remainder_empty_of_ok
      (fuel := fuel) (code := code) (program := program) hok with
    ⟨rest, haux, hbits, hrefs⟩
  have haux' :
      decodeCp0AllAux (fuel + extra) code = .ok (program, rest) :=
    decodeCp0AllAux_ok_mono_fuel_of_remainder_empty_bits
      (fuel := fuel) (extra := extra) (code := code) (program := program) (rest := rest)
      haux hbits
  exact decodeCp0All_ok_of_aux_ok_remainder_empty
    (fuel := fuel + extra) (code := code) (program := program) (rest := rest)
    haux' hbits hrefs

theorem decodeCp0AllFromCell_ok_mono_fuel
    (fuel extra : Nat) (code : Cell) (program : List Instr)
    (hok : decodeCp0AllFromCell fuel code = .ok program) :
    decodeCp0AllFromCell (fuel + extra) code = .ok program := by
  simpa [decodeCp0AllFromCell] using
    decodeCp0All_ok_mono_fuel
      (fuel := fuel) (extra := extra) (code := Slice.ofCell code) (program := program) hok

theorem VmState.execDecodedCp0_ok_of_decode (host : Host) (fuel : Nat) (code : Cell) (st : VmState)
    (program : List Instr)
    (hdecode : decodeCp0AllFromCell fuel code = .ok program) :
    VmState.execDecodedCp0 host fuel code st = .ok (VmState.execProgram host program st) := by
  unfold VmState.execDecodedCp0
  rw [hdecode]
  rfl

theorem assembleAndDecodeCp0_eq_decode (fuel : Nat) (program : List Instr) (code : Cell)
    (hasm : assembleCp0 program = .ok code) :
    assembleAndDecodeCp0 fuel program = decodeCp0AllFromCell fuel code := by
  unfold assembleAndDecodeCp0
  rw [hasm]
  rfl

theorem assembleAndDecodeCp0_ok_iff_decode_of_assemble
    (fuel : Nat) (program decoded : List Instr) (code : Cell)
    (hasm : assembleCp0 program = .ok code) :
    assembleAndDecodeCp0 fuel program = .ok decoded ↔
      decodeCp0AllFromCell fuel code = .ok decoded := by
  simp [assembleAndDecodeCp0_eq_decode (fuel := fuel) (program := program) (code := code) hasm]

theorem assembleAndDecodeCp0_ok_mono_fuel
    (fuel extra : Nat) (program decoded : List Instr)
    (hok : assembleAndDecodeCp0 fuel program = .ok decoded) :
    assembleAndDecodeCp0 (fuel + extra) program = .ok decoded := by
  cases hasm : assembleCp0 program with
  | error e =>
      unfold assembleAndDecodeCp0 at hok
      rw [hasm] at hok
      change (Except.error e : Except Excno (List Instr)) = Except.ok decoded at hok
      cases hok
  | ok code =>
      have hdecode : decodeCp0AllFromCell fuel code = .ok decoded := by
        simpa [assembleAndDecodeCp0_eq_decode (fuel := fuel) (program := program) (code := code) hasm]
          using hok
      have hdecode' : decodeCp0AllFromCell (fuel + extra) code = .ok decoded :=
        decodeCp0AllFromCell_ok_mono_fuel
          (fuel := fuel) (extra := extra) (code := code) (program := decoded) hdecode
      simpa [assembleAndDecodeCp0_eq_decode (fuel := fuel + extra) (program := program) (code := code) hasm]
        using hdecode'

theorem VmState.execDecodedCp0_ok_of_assembleAndDecode
    (host : Host) (fuel : Nat) (st : VmState)
    (program decoded : List Instr) (code : Cell)
    (hasm : assembleCp0 program = .ok code)
    (hdecode : assembleAndDecodeCp0 fuel program = .ok decoded) :
    VmState.execDecodedCp0 host fuel code st = .ok (VmState.execProgram host decoded st) := by
  have hdecodeCode : decodeCp0AllFromCell fuel code = .ok decoded := by
    simpa [assembleAndDecodeCp0_eq_decode (fuel := fuel) (program := program) (code := code) hasm]
      using hdecode
  exact VmState.execDecodedCp0_ok_of_decode
    (host := host) (fuel := fuel) (code := code) (st := st) (program := decoded) hdecodeCode

theorem VmState.execDecodedCp0_ok_of_assembleRoundtrip
    (host : Host) (fuel : Nat) (st : VmState)
    (program : List Instr) (code : Cell)
    (hasm : assembleCp0 program = .ok code)
    (hdecode : assembleAndDecodeCp0 fuel program = .ok program) :
    VmState.execDecodedCp0 host fuel code st = .ok (VmState.execProgram host program st) := by
  exact VmState.execDecodedCp0_ok_of_assembleAndDecode
    (host := host) (fuel := fuel) (st := st)
    (program := program) (decoded := program) (code := code) hasm hdecode

theorem assembleDecodeMatches_of_decodeEq (fuel : Nat) (program decoded : List Instr)
    (hdecode : assembleAndDecodeCp0 fuel program = .ok decoded)
    (hEq : (decoded == program) = true) :
    assembleDecodeMatches fuel program = true := by
  simp [assembleDecodeMatches, hdecode, hEq]

end TvmLean
