import TvmLean.Core.Exec

namespace TvmLean

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

structure TraceEntry where
  step : Nat
  event : String
  cp : Int
  cc_before : String
  cc_after : String
  gas_before : Int
  gas_after : Int
  stack_before : String
  stack_after : String
  deriving Repr

instance : Inhabited TraceEntry where
  default :=
    { step := 0
      event := ""
      cp := 0
      cc_before := ""
      cc_after := ""
      gas_before := 0
      gas_after := 0
      stack_before := ""
      stack_after := "" }

def stackStr (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def Stack.pretty (s : Stack) : String :=
  stackStr s

def Slice.peekByteHex (s : Slice) : String :=
  if s.haveBits 8 then
    let b := bitsToNat (s.readBits 8)
    let hex := String.mk (Nat.toDigits 16 b)
    let hex := if b < 16 then "0" ++ hex else hex
    s!"0x{hex}"
  else
    "<eof>"

def natToHexPad (n : Nat) (digits : Nat) : String :=
  let hex := String.mk (Nat.toDigits 16 n)
  if hex.length ≥ digits then
    hex
  else
    String.mk (List.replicate (digits - hex.length) '0') ++ hex

def Slice.peekWord16Hex (s : Slice) : String :=
  if s.haveBits 16 then
    s!"0x{natToHexPad (bitsToNat (s.readBits 16)) 4}"
  else
    "<eof>"

def VmState.ccSummary (cc : Continuation) : String :=
  match cc with
  | .quit n => s!"quit {n}"
  | .excQuit => "excquit"
  | .whileCond _ _ _ => "whileCond"
  | .whileBody _ _ _ => "whileBody"
  | .untilBody _ _ => "untilBody"
  | .envelope _ _ _ => "envelope"
  | .ordinary code _ _ _ =>
      s!"ord(bitPos={code.bitPos},refPos={code.refPos},bitsRem={code.bitsRemaining},refsRem={code.refsRemaining},next8={code.peekByteHex},next16={code.peekWord16Hex})"

def VmState.outOfGasHalt (st : VmState) : StepResult :=
  -- Match C++ unhandled out-of-gas: clear stack and push `gas_consumed()`
  -- (which may exceed the base/limit if `gas_remaining` went negative).
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  StepResult.halt Excno.outOfGas.toInt st'

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

def VmState.step (st : VmState) : StepResult :=
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
            let st0 := st.throwException e.toInt
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
              let (res, st1) := (execInstr instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    st1.outOfGasHalt
                  else
                    .continue st1
              | .error e =>
                  -- TVM behavior: convert VM errors into an exception jump to c2.
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    stExcGas.outOfGasHalt
                  else
                .continue stExcGas

def VmState.stepTrace (st : VmState) (step : Nat) : TraceEntry × StepResult :=
  let mk (event : String) (stAfter : VmState) (res : StepResult) : TraceEntry × StepResult :=
    ({ step
       event
       cp := st.cp
       cc_before := VmState.ccSummary st.cc
       cc_after := VmState.ccSummary stAfter.cc
       gas_before := st.gas.gasRemaining
       gas_after := stAfter.gas.gasRemaining
       stack_before := stackStr st.stack
       stack_after := stackStr stAfter.stack },
     res)
  match st.cc with
  | .quit n =>
      let res := StepResult.halt (~~~ n) st
      mk s!"quit({n})" st res
  | .excQuit =>
      let action : VM Int := do
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res0, st') := (action.run st)
      let n : Int :=
        match res0 with
        | .ok n => n
        | .error e => e.toInt
      let res := StepResult.halt (~~~ n) st'
      mk s!"excquit({n})" st' res
  | .whileCond cond body after =>
      let action : VM Bool := do
        let b ← VM.popBool
        if b then
          modify fun st => { st with regs := { st.regs with c0 := .whileBody cond body after }, cc := body }
        else
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        return b
      let (res0, st1) := (action.run st)
      let (event, res) :=
        match res0 with
        | .ok b => (s!"while_cond({b})", StepResult.continue st1)
        | .error e =>
            let stExc := st1.throwException e.toInt
            let stExcGas := stExc.consumeGas exceptionGasPrice
            if decide (stExcGas.gas.gasRemaining < 0) then
              (s!"while_cond_error({reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
            else
              (s!"while_cond_error({reprStr e})", StepResult.continue stExcGas)
      let stAfter :=
        match res with
        | .continue st' => st'
        | .halt _ st' => st'
      mk event stAfter res
  | .whileBody cond body after =>
      let st1 := { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
      let res := StepResult.continue st1
      mk "while_body" st1 res
  | .untilBody body after =>
      let action : VM Bool := do
        let b ← VM.popBool
        if b then
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        else
          if body.hasC0 then
            modify fun st => { st with cc := body }
          else
            modify fun st => { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
        return b
      let (res0, st1) := (action.run st)
      let (event, res) :=
        match res0 with
        | .ok b => (s!"until_body({b})", StepResult.continue st1)
        | .error e =>
            let stExc := st1.throwException e.toInt
            let stExcGas := stExc.consumeGas exceptionGasPrice
            if decide (stExcGas.gas.gasRemaining < 0) then
              (s!"until_body_error({reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
            else
              (s!"until_body_error({reprStr e})", StepResult.continue stExcGas)
      let stAfter :=
        match res with
        | .continue st' => st'
        | .halt _ st' => st'
      mk event stAfter res
  | .envelope ext cregs cdata =>
      let st1 := st.applyCregsCdata cregs cdata
      let stAfter := { st1 with cc := ext }
      let res := StepResult.continue stAfter
      mk "envelope" stAfter res
  | .ordinary code saved cregs cdata =>
      -- Apply pending continuation regs and closure stack (once), matching `VmState.step`.
      let st2 := st.applyCregsCdata cregs cdata
      let cdata' : OrdCdata := { cdata with stack := #[], nargs := -1 }
      let st : VmState := { st2 with cc := .ordinary code saved OrdCregs.empty cdata' }
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          let st0 := st.consumeGas implicitRetGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              let (res0, st1) := (VM.ret).run st0
              match res0 with
              | .ok _ =>
                  .continue st1
              | .error e =>
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    stExcGas.outOfGasHalt
                  else
                    .continue stExcGas
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_ret" stAfter res
        else
          let st0 := st.consumeGas implicitJmpRefGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else if code.refPos < code.cell.refs.size then
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
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_jmpref" stAfter res
      else
        let decoded : Except Excno (Instr × Nat × Slice) :=
          if st.cp = 0 then
            decodeCp0WithBits code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            let st0 := st.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            let res :=
              if decide (st0.gas.gasRemaining < 0) then
                st0.outOfGasHalt
              else
                .continue st0
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk s!"decode_error({e})" stAfter res
        | .ok (instr, totBits, rest) =>
            let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
            let stGas := st0.consumeGas (instrGas instr totBits)
            let (event, res) :=
              if decide (stGas.gas.gasRemaining < 0) then
                (s!"exec({instr.pretty}) out_of_gas", stGas.outOfGasHalt)
              else
                let (res1, st1) := (execInstr instr).run stGas
                match res1 with
                | .ok _ =>
                    if decide (st1.gas.gasRemaining < 0) then
                      (s!"exec({instr.pretty}) out_of_gas", st1.outOfGasHalt)
                    else
                      (s!"exec({instr.pretty})", .continue st1)
                | .error e =>
                    let stExc := st1.throwException e.toInt
                    let stExcGas := stExc.consumeGas exceptionGasPrice
                    if decide (stExcGas.gas.gasRemaining < 0) then
                      (s!"exec_error({instr.pretty},{reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
                    else
                      (s!"exec_error({instr.pretty},{reprStr e})", .continue stExcGas)
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk event stAfter res

def VmState.tryCommit (st : VmState) : Bool × VmState :=
  -- C++ also checks `level == 0`; our MVP has only ordinary cells (level 0).
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def VmState.runTrace (fuel : Nat) (st : VmState) (maxTrace : Nat := 200) :
    StepResult × Array TraceEntry × Bool :=
  Id.run do
    let mut stCur := st
    let mut fuelCur := fuel
    let mut step : Nat := 0
    let mut trace : Array TraceEntry := #[]
    let mut pos : Nat := 0
    let mut wrapped : Bool := false
    let mut res : StepResult := .continue stCur

    while fuelCur > 0 do
      let (entry, stepRes) := stCur.stepTrace step
      if maxTrace > 0 then
        if trace.size < maxTrace then
          trace := trace.push entry
        else
          trace := trace.set! pos entry
          pos := (pos + 1) % maxTrace
          wrapped := true

      match stepRes with
      | .continue st' =>
          stCur := st'
          res := .continue st'
          fuelCur := fuelCur - 1
          step := step + 1
      | .halt exitCode st' =>
          res := .halt exitCode st'
          stCur := st'
          fuelCur := 0

    match res with
    | .continue st' =>
        res := .halt (Excno.fatal.toInt) st'
    | .halt _ _ => pure ()

    -- Mirror the C++ commit wrapper shape; precise commit checks come later.
    let res' :=
      match res with
      | .continue st' => .halt (Excno.fatal.toInt) st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

    let traceOut :=
      if wrapped && trace.size > 0 then
        let n := trace.size
        Array.ofFn (n := n) fun i =>
          let idx := (pos + i.1) % n
          trace[idx]!
      else
        trace

    return (res', traceOut, wrapped)

def VmState.run (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step with
      | .continue st' => VmState.run fuel st'
      | .halt exitCode st' =>
          -- Mirror the C++ commit wrapper shape; precise commit checks come later.
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

/-! ### Proof scaffolding (Milestone 1, mostly `sorry`) -/

def WF_Int : IntVal → Prop
  | .nan => True
  | .num n =>
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      lo ≤ n ∧ n < hi

def WF_Cell (c : Cell) : Prop :=
  c.bits.size ≤ 1023 ∧ c.refs.size ≤ 4

def WF_Slice (s : Slice) : Prop :=
  WF_Cell s.cell ∧ s.bitPos ≤ s.cell.bits.size ∧ s.refPos ≤ s.cell.refs.size

def WF_Builder (b : Builder) : Prop :=
  b.bits.size ≤ 1023 ∧ b.refs.size ≤ 4

def WF_Tuple (t : Array Value) : Prop :=
  t.size ≤ 255

def WF_Value : Value → Prop
  | .int i => WF_Int i
  | .cell c => WF_Cell c
  | .slice s => WF_Slice s
  | .builder b => WF_Builder b
  | .tuple t => WF_Tuple t
  | .cont _ => True
  | .null => True

def WF_Gas (g : GasLimits) : Prop :=
  g.gasLimit ≤ g.gasMax ∧ g.gasBase = g.gasLimit + g.gasCredit ∧ g.gasRemaining ≤ g.gasBase

def WF_Regs (r : Regs) : Prop :=
  WF_Cell r.c4 ∧ WF_Cell r.c5 ∧ WF_Tuple r.c7

def WF_State (st : VmState) : Prop :=
  (∀ v ∈ st.stack.toList, WF_Value v) ∧ WF_Regs st.regs ∧ WF_Gas st.gas

theorem step_preserves_wf {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem run_preserves_wf {fuel : Nat} {st : VmState} :
    WF_State st →
      match VmState.run fuel st with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem step_progress {st : VmState} :
    WF_State st →
      match st.step with
      | .continue _ => True
      | .halt _ _ => True := by
  sorry

theorem step_gas_monotone {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining
      | .halt _ st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining := by
  sorry

end TvmLean
