import TvmLean.Semantics.Step.Run

namespace TvmLean

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
  | .repeatBody _ _ _ => "repeatBody"
  | .againBody _ => "againBody"
  | .envelope _ _ _ => "envelope"
  | .ordinary code _ _ _ =>
      s!"ord(bitPos={code.bitPos},refPos={code.refPos},bitsRem={code.bitsRemaining},refsRem={code.refsRemaining},next8={code.peekByteHex},next16={code.peekWord16Hex})"

def VmState.stepTrace (host : Host) (st : VmState) (step : Nat) : TraceEntry × StepResult :=
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
  | .repeatBody body after count =>
      let (event, st1) :=
        if count = 0 then
          match after with
          | .ordinary code saved cregs cdata =>
              ("repeat_body(done)", { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata })
          | _ =>
              ("repeat_body(done)", { st with cc := after })
        else if body.hasC0 then
          ("repeat_body(body_has_c0)", { st with cc := body })
        else
          ("repeat_body(step)", { st with regs := { st.regs with c0 := .repeatBody body after (count - 1) }, cc := body })
      let res := StepResult.continue st1
      mk event st1 res
  | .againBody body =>
      let (event, st1) :=
        if body.hasC0 then
          ("again_body(body_has_c0)", { st with cc := body })
        else
          ("again_body(step)", { st with regs := { st.regs with c0 := .againBody body }, cc := body })
      let res := StepResult.continue st1
      mk event st1 res
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
              st0.gasCheckFailed
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
              st0.gasCheckFailed
            else if code.refPos < code.cell.refs.size then
              let refCell := code.cell.refs[code.refPos]!
              let st1 := st0.registerCellLoad refCell
              if decide (st1.gas.gasRemaining < 0) then
                st1.gasCheckFailed
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
                (s!"exec({instr.pretty}) out_of_gas", stGas.gasCheckFailed)
              else
                let (res1, st1) := (execInstr host instr).run stGas
                match res1 with
                | .ok _ =>
                    if decide (st1.gas.gasRemaining < 0) then
                      (s!"exec({instr.pretty}) out_of_gas", st1.gasCheckFailed)
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

def VmState.runTrace (host : Host) (fuel : Nat) (st : VmState) (maxTrace : Nat := 200) :
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
      let (entry, stepRes) := stCur.stepTrace host step
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

end TvmLean
