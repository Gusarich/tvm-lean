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

theorem assembleDecodeMatches_of_decodeEq (fuel : Nat) (program decoded : List Instr)
    (hdecode : assembleAndDecodeCp0 fuel program = .ok decoded)
    (hEq : (decoded == program) = true) :
    assembleDecodeMatches fuel program = true := by
  simp [assembleDecodeMatches, hdecode, hEq]

end TvmLean
