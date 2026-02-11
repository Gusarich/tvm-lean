import TvmLean.Semantics.Exec.Dispatch

namespace TvmLean

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

def VmState.outOfGasHalt (st : VmState) : StepResult :=
  -- Match `VmState::run()` behavior: unhandled out-of-gas returns the plain
  -- exception number (13) and leaves `stack=[gas_consumed]`.  Note that the
  -- Fift `runvmx` primitive applies `~` to this return value, so the oracle
  -- observes `-14` for out-of-gas.
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  StepResult.halt Excno.outOfGas.toInt st'

/-- Mirror C++ gas.check() → VmNoGas → throw_exception(out_of_gas) path:
    treat gas exhaustion as an out-of-gas exception, charge exception_gas_price,
    then halt with 13 (Fift `runvmx` observes `~13 = -14`).
    Used for non-error paths where gas went negative. -/
def VmState.gasCheckFailed (st : VmState) : StepResult :=
  let stExc := st.throwException Excno.outOfGas.toInt
  let stExcGas := stExc.consumeGas exceptionGasPrice
  stExcGas.outOfGasHalt

def VmState.applyCregsCdata (st : VmState) (cregs : OrdCregs) (cdata : OrdCdata) : VmState :=
  -- Mirrors C++ `adjust_cr(save)` + `adjust_jump_cont` stack truncation/merge on jump/call.
  let regs0 := st.regs
  let regs1 := match cregs.c0 with | some c0 => { regs0 with c0 := c0 } | none => regs0
  let regs2 := match cregs.c1 with | some c1 => { regs1 with c1 := c1 } | none => regs1
  let regs3 := match cregs.c2 with | some c2 => { regs2 with c2 := c2 } | none => regs2
  let regs4 := match cregs.c3 with | some c3 => { regs3 with c3 := c3 } | none => regs3
  let regs5 := match cregs.c4 with | some c4 => { regs4 with c4 := c4 } | none => regs4
  let regs6 := match cregs.c5 with | some c5 => { regs5 with c5 := c5 } | none => regs5
  let regs7 := match cregs.c7 with | some c7 => { regs6 with c7 := c7 } | none => regs6
  let st1 : VmState := { st with regs := regs7 }
  let stack0 := st1.stack
  let (stack1, truncated) : Stack × Bool :=
    if decide (0 ≤ cdata.nargs) then
      let copy : Nat := cdata.nargs.toNat
      if copy < stack0.size then
        (stack0.extract (stack0.size - copy) stack0.size, true)
      else
        (stack0, false)
    else
      (stack0, false)
  let st1' : VmState := { st1 with stack := stack1 }
  if cdata.stack.isEmpty then
    -- C++ `adjust_jump_cont` charges stack gas only if it actually truncates the stack.
    if truncated then
      st1'.consumeStackGas stack1.size
    else
      st1'
  else
    -- C++ `adjust_jump_cont` / `call` merges the continuation's saved stack and then charges stack gas for
    -- the resulting depth via `consume_stack_gas(new_stk)`.
    let newStack := cdata.stack ++ stack1
    ( { st1' with stack := newStack } ).consumeStackGas newStack.size

def cp0InvOpcodeGasBits (code : Slice) : Nat :=
  -- Approximate C++ opcode-table charging for invalid/too-short opcodes:
  -- decode the same prefix after zero-padding bits so short fixed/ext opcodes
  -- report their declared bit length (e.g. 16/24) instead of falling back to 8.
  let bits0 : BitString := code.readBits code.bitsRemaining
  -- Some cp0 opcodes (e.g. PUSHSLICE_REFS/LONG, PUSHCONT) validate the presence of
  -- inline payload bits and refs *after* their header is recognized. When the code
  -- slice is truncated in the payload, C++ still charges based on the matched
  -- opcode entry width (header bits), not the 8-bit fallback.
  --
  -- To approximate this, always pad enough bits so the decoder can proceed past
  -- payload-length guards and report the header width.
  let padBitsTo : Nat := 2048
  let bitsPad : BitString :=
    if bits0.size < padBitsTo then
      bits0 ++ Array.replicate (padBitsTo - bits0.size) false
    else
      bits0
  let refs0 : Array Cell := code.cell.refs.extract code.refPos code.cell.refs.size
  let refsPad : Array Cell :=
    if refs0.size < 4 then
      refs0 ++ Array.replicate (4 - refs0.size) Cell.empty
    else
      refs0
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary bitsPad refsPad)) with
  | .ok (_instr, totBits, _rest) => totBits
  | .error _ =>
      -- If we still can't match a real opcode-table entry even after padding,
      -- treat this as a dummy `inv_opcode` dispatch (C++ charges `gas_per_instr`
      -- without per-bit cost in this case).
      0

def VmState.step (host : Host) (st : VmState) : StepResult :=
  match st.cc with
  | .quit n =>
      .halt (~~~ n) st
  | .excQuit =>
      let action : VM Int := do
        -- Match `pop_smallint_range(0xffff)` behavior closely enough for MVP.
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res, st') := (action.run st)
      let n : Int :=
        match res with
        | .ok n => n
        | .error e => e.toInt
      .halt (~~~ n) st'
  | .whileCond cond body after =>
      let action : VM Unit := do
        if (← VM.popBool) then
          modify fun st => { st with regs := { st.regs with c0 := .whileBody cond body after }, cc := body }
        else
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
      let (res, st') := (action.run st)
      match res with
      | .ok _ =>
          .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            stExcGas.outOfGasHalt
          else
            .continue stExcGas
  | .whileBody cond body after =>
      .continue { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | .untilBody body after =>
      let action : VM Unit := do
        if (← VM.popBool) then
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        else
          -- C++ `UntilCont::jump`: if `body` doesn't have `c0`, re-install this until continuation into `c0`
          -- because `RET` swaps `c0 := quit0` when returning to `c0`.
          if body.hasC0 then
            modify fun st => { st with cc := body }
          else
            modify fun st => { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
      let (res, st') := (action.run st)
      match res with
      | .ok _ =>
          .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            stExcGas.outOfGasHalt
          else
            .continue stExcGas
  | .repeatBody body after count =>
      if count = 0 then
        match after with
        | .ordinary code saved cregs cdata =>
            .continue { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
        | _ =>
            .continue { st with cc := after }
      else if body.hasC0 then
        .continue { st with cc := body }
      else
        let count' := count - 1
        .continue { st with regs := { st.regs with c0 := .repeatBody body after count' }, cc := body }
  | .againBody body =>
      if body.hasC0 then
        .continue { st with cc := body }
      else
        .continue { st with regs := { st.regs with c0 := .againBody body }, cc := body }
  | .envelope ext cregs cdata =>
      -- Mirrors C++ `ArgContExt::jump`: apply saved control regs, closure stack and nargs, then jump to `ext`.
      let st := st.applyCregsCdata cregs cdata
      .continue { st with cc := ext }
  | .ordinary code saved cregs cdata =>
      -- Apply pending continuation control regs (MVP: c0,c1,c2,c3,c4,c5,c7), once.
      let st2 := st.applyCregsCdata cregs cdata
      -- Closure stack / nargs are applied once on entry.
      let cdata' : OrdCdata := { cdata with stack := #[], nargs := -1 }
      let st : VmState := { st2 with cc := .ordinary code saved OrdCregs.empty cdata' }
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          -- Implicit RET.
          let st0 := st.consumeGas implicitRetGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            let (res, st1) := (VM.ret).run st0
            match res with
            | .ok _ =>
                .continue st1
            | .error e =>
                let stExc := st1.throwException e.toInt
                let stExcGas := stExc.consumeGas exceptionGasPrice
                if decide (stExcGas.gas.gasRemaining < 0) then
                  stExcGas.outOfGasHalt
                else
                  .continue stExcGas
        else
          -- Implicit JMPREF to the first reference.
          let st0 := st.consumeGas implicitJmpRefGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            if code.refPos < code.cell.refs.size then
              let refCell := code.cell.refs[code.refPos]!
              let st1 := st0.registerCellLoad refCell
              if decide (st1.gas.gasRemaining < 0) then
                st1.outOfGasHalt
              else
                .continue { st1 with cc := .ordinary (Slice.ofCell refCell) (.quit 0) OrdCregs.empty OrdCdata.empty }
            else
              let stExc := st0.throwException Excno.cellUnd.toInt
              let stExcGas := stExc.consumeGas exceptionGasPrice
              if decide (stExcGas.gas.gasRemaining < 0) then
                stExcGas.outOfGasHalt
              else
                .continue stExcGas
      else
        let decoded : Except Excno (Instr × Nat × Slice) :=
          if st.cp = 0 then
            decodeCp0WithBits code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            -- Align with C++ opcode-table behavior: some invalid/too-short opcode paths
            -- charge one instruction slot before raising `inv_opcode`.
            let st0 :=
              if e = .invOpcode ∧ code.bitsRemaining > 0 then
                let invalBits : Nat := cp0InvOpcodeGasBits code
                st.consumeGas (gasPerInstr + Int.ofNat invalBits)
              else
                st
            let st0 := st0.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              .continue st0
        | .ok (instr, totBits, rest) =>
            let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
            let stGas := st0.consumeGas (instrGas instr totBits)
            if decide (stGas.gas.gasRemaining < 0) then
              stGas.outOfGasHalt
            else
              let (res, st1) := (execInstr host instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    -- C++ gas.check() after step → VmNoGas → propagates to run(),
                    -- bypassing throw_exception.  No exception_gas charged.
                    st1.outOfGasHalt
                  else
                    .continue st1
              | .error e =>
                  if e = .outOfGas then
                    -- VmNoGas thrown mid-instruction (e.g. from consume_gas during
                    -- cell load).  Propagates to run(), no exception_gas charged.
                    st1.outOfGasHalt
                  else
                    -- TVM behavior: convert VM errors into an exception jump to c2.
                    let stExc := st1.throwException e.toInt
                    let stExcGas := stExc.consumeGas exceptionGasPrice
                    if decide (stExcGas.gas.gasRemaining < 0) then
                      stExcGas.outOfGasHalt
                    else
                      .continue stExcGas

end TvmLean
