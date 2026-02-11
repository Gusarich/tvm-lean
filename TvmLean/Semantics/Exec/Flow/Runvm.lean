import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Stack
import TvmLean.Semantics.Exec.Cont
import TvmLean.Semantics.Exec.Cell
import TvmLean.Semantics.Exec.Flow.Setcp
import TvmLean.Semantics.Exec.Flow.Ifret
import TvmLean.Semantics.Exec.Flow.Ifnotret
import TvmLean.Semantics.Exec.Flow.IfretAlt
import TvmLean.Semantics.Exec.Flow.If
import TvmLean.Semantics.Exec.Flow.Ifnot
import TvmLean.Semantics.Exec.Flow.PushSliceConst
import TvmLean.Semantics.Exec.Flow.PushCont
import TvmLean.Semantics.Exec.Flow.PushRef
import TvmLean.Semantics.Exec.Flow.PushRefSlice
import TvmLean.Semantics.Exec.Flow.PushRefCont
import TvmLean.Semantics.Exec.Flow.Execute
import TvmLean.Semantics.Exec.Flow.Jmpx
import TvmLean.Semantics.Exec.Flow.CallxArgs
import TvmLean.Semantics.Exec.Flow.JmpxArgs
import TvmLean.Semantics.Exec.Flow.Callcc
import TvmLean.Semantics.Exec.Flow.CallxVarArgs
import TvmLean.Semantics.Exec.Flow.Ret
import TvmLean.Semantics.Exec.Flow.RetAlt
import TvmLean.Semantics.Exec.Flow.RetBool
import TvmLean.Semantics.Exec.Flow.RetArgs
import TvmLean.Semantics.Exec.Flow.RetVarArgs
import TvmLean.Semantics.Exec.Flow.RetData
import TvmLean.Semantics.Exec.Flow.JmpxVarArgs
import TvmLean.Semantics.Exec.Flow.JmpxData
import TvmLean.Semantics.Exec.Flow.Ifjmp
import TvmLean.Semantics.Exec.Flow.Ifnotjmp
import TvmLean.Semantics.Exec.Flow.Ifelse
import TvmLean.Semantics.Exec.Flow.Ifref
import TvmLean.Semantics.Exec.Flow.Ifnotref
import TvmLean.Semantics.Exec.Flow.Ifjmpref
import TvmLean.Semantics.Exec.Flow.Ifnotjmpref
import TvmLean.Semantics.Exec.Flow.IfrefElse
import TvmLean.Semantics.Exec.Flow.IfelseRef
import TvmLean.Semantics.Exec.Flow.IfrefElseRef
import TvmLean.Semantics.Exec.Flow.IfBitJmp
import TvmLean.Semantics.Exec.Flow.CallRef
import TvmLean.Semantics.Exec.Flow.JmpRef
import TvmLean.Semantics.Exec.Flow.CallDict
import TvmLean.Semantics.Exec.Flow.PrepareDict
import TvmLean.Semantics.Exec.Flow.Until
import TvmLean.Semantics.Exec.Flow.While
import TvmLean.Semantics.Exec.Flow.LoopExt
import TvmLean.Semantics.Exec.Flow.Blkdrop2
import TvmLean.Semantics.Exec.Flow.Blkdrop
import TvmLean.Semantics.Exec.Flow.Drop2
import TvmLean.Semantics.Exec.Arith
import TvmLean.Semantics.Exec.Tuple
import TvmLean.Semantics.Exec.CellOp
import TvmLean.Semantics.Exec.TonEnv
import TvmLean.Semantics.Exec.Crypto
import TvmLean.Semantics.Exec.Msg
import TvmLean.Semantics.Exec.Misc
import TvmLean.Semantics.Exec.Debug
import TvmLean.Semantics.Exec.Exception
import TvmLean.Semantics.Exec.Dict

namespace TvmLean

def popNatUpToSigned (max : Nat) : VM Nat :=
  VM.popNatUpTo max

def popGasRange : VM Int := do
  let n ← VM.popIntFinite
  if n < 0 ∨ n > GasLimits.infty then
    throw .rangeChk
  return n

def VM.popTuple : VM (Array Value) := do
  let v ← VM.pop
  match v with
  | .tuple t => return t
  | _ => throw .typeChk

def childFuelDefault : Nat := 50_000

inductive ChildStepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

def applyCregsCdata (st : VmState) (cregs : OrdCregs) (cdata : OrdCdata) : VmState :=
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
    if truncated then
      st1'.consumeStackGas stack1.size
    else
      st1'
  else
    let newStack := cdata.stack ++ stack1
    ({ st1' with stack := newStack }).consumeStackGas newStack.size

def tryCommit (st : VmState) : Bool × VmState :=
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def cp0InvOpcodeGasBitsRunvm (code : Slice) : Nat :=
  -- Mirror the main-step fallback (`cp0InvOpcodeGasBits`) for child VM decode errors.
  -- C++ may charge one opcode slot for invalid/too-short prefixes.
  let bits0 : BitString := code.readBits code.bitsRemaining
  let bitsPad : BitString :=
    if bits0.size < 24 then
      bits0 ++ Array.replicate (24 - bits0.size) false
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
      if code.bitsRemaining < 4 then 16 else 8

set_option maxHeartbeats 1000000 in
def execInstrFlowChildNoRunvm (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrFlowSetcp i <|
  execInstrFlowIfret i <|
  execInstrFlowIfnotret i <|
  execInstrFlowIfretAlt i <|
  execInstrFlowIf i <|
  execInstrFlowIfnot i <|
  execInstrFlowPushSliceConst i <|
  execInstrFlowPushCont i <|
  execInstrFlowPushRef i <|
  execInstrFlowPushRefSlice i <|
  execInstrFlowPushRefCont i <|
  execInstrFlowExecute i <|
  execInstrFlowJmpx i <|
  execInstrFlowCallxArgs i <|
  execInstrFlowJmpxArgs i <|
  execInstrFlowCallcc i <|
  execInstrFlowCallxVarArgs i <|
  execInstrFlowRet i <|
  execInstrFlowRetAlt i <|
  execInstrFlowRetBool i <|
  execInstrFlowRetArgs i <|
  execInstrFlowRetVarArgs i <|
  execInstrFlowRetData i <|
  execInstrFlowJmpxVarArgs i <|
  execInstrFlowJmpxData i <|
  execInstrFlowIfjmp i <|
  execInstrFlowIfnotjmp i <|
  execInstrFlowIfelse i <|
  execInstrFlowIfref i <|
  execInstrFlowIfnotref i <|
  execInstrFlowIfjmpref i <|
  execInstrFlowIfnotjmpref i <|
  execInstrFlowIfrefElse i <|
  execInstrFlowIfelseRef i <|
  execInstrFlowIfrefElseRef i <|
  execInstrFlowIfBitJmp i <|
  execInstrFlowCallRef i <|
  execInstrFlowJmpRef i <|
  execInstrFlowCallDict i <|
  execInstrFlowPrepareDict i <|
  execInstrFlowUntil i <|
  execInstrFlowWhile i <|
  execInstrFlowLoopExt i <|
  execInstrFlowBlkdrop2 i <|
  execInstrFlowBlkdrop i <|
  execInstrFlowDrop2 i <|
    next

set_option maxHeartbeats 1000000 in
def execInstrChildNoRunvm (host : Host) (i : Instr) : VM Unit :=
  execInstrStack host i <|
    execInstrCont host i <|
      execInstrCell host i <|
        execInstrFlowChildNoRunvm host i <|
          execInstrArith host i <|
            execInstrTuple host i <|
              execInstrCellOp host i <|
                execInstrTonEnv host i <|
                  execInstrCrypto host i <|
                    execInstrMsg host i <|
                      execInstrMisc host i <|
                      execInstrDebug host i <|
                      execInstrException host i <|
                        execInstrDict host i <|
                          throw .invOpcode

def outOfGasHalt (st : VmState) : ChildStepResult :=
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  ChildStepResult.halt (~~~ Excno.outOfGas.toInt) st'

/-- Mirror C++ gas.check() → throw_exception(out_of_gas) for child VM. -/
private def gasCheckFailed (st : VmState) : ChildStepResult :=
  let stExc := st.throwException Excno.outOfGas.toInt
  let stExcGas := stExc.consumeGas exceptionGasPrice
  outOfGasHalt stExcGas

def childStep (host : Host) (st : VmState) : ChildStepResult :=
  match st.cc with
  | .quit n =>
      .halt (~~~ n) st
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
      | .ok _ => .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            outOfGasHalt stExcGas
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
          if body.hasC0 then
            modify fun st => { st with cc := body }
          else
            modify fun st => { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
      let (res, st') := (action.run st)
      match res with
      | .ok _ => .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            outOfGasHalt stExcGas
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
      let st := applyCregsCdata st cregs cdata
      .continue { st with cc := ext }
  | .ordinary code saved cregs cdata =>
      let st2 := applyCregsCdata st cregs cdata
      let cdata' : OrdCdata := { cdata with stack := #[], nargs := -1 }
      let st : VmState := { st2 with cc := .ordinary code saved OrdCregs.empty cdata' }
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          let st0 := st.consumeGas implicitRetGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            outOfGasHalt st0
          else
            let (res, st1) := (VM.ret).run st0
            match res with
            | .ok _ => .continue st1
            | .error e =>
                let stExc := st1.throwException e.toInt
                let stExcGas := stExc.consumeGas exceptionGasPrice
                if decide (stExcGas.gas.gasRemaining < 0) then
                  outOfGasHalt stExcGas
                else
                  .continue stExcGas
        else
          let st0 := st.consumeGas implicitJmpRefGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            outOfGasHalt st0
          else if code.refPos < code.cell.refs.size then
            let refCell := code.cell.refs[code.refPos]!
            let st1 := st0.registerCellLoad refCell
            if decide (st1.gas.gasRemaining < 0) then
              outOfGasHalt st1
            else
              .continue { st1 with cc := .ordinary (Slice.ofCell refCell) (.quit 0) OrdCregs.empty OrdCdata.empty }
          else
            let stExc := st0.throwException Excno.cellUnd.toInt
            let stExcGas := stExc.consumeGas exceptionGasPrice
            if decide (stExcGas.gas.gasRemaining < 0) then
              outOfGasHalt stExcGas
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
            let st0 :=
              if e = .invOpcode ∧ code.bitsRemaining > 0 then
                let invalBits : Nat := cp0InvOpcodeGasBitsRunvm code
                st.consumeGas (gasPerInstr + Int.ofNat invalBits)
              else
                st
            let st0 := st0.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              outOfGasHalt st0
            else
              .continue st0
        | .ok (instr, totBits, rest) =>
            let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
            let stGas := st0.consumeGas (instrGas instr totBits)
            if decide (stGas.gas.gasRemaining < 0) then
              outOfGasHalt stGas
            else
              let (res, st1) := (execInstrChildNoRunvm host instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    outOfGasHalt st1
                  else
                    .continue st1
              | .error e =>
                  if e = .outOfGas then
                    outOfGasHalt st1
                  else
                    let stExc := st1.throwException e.toInt
                    let stExcGas := stExc.consumeGas exceptionGasPrice
                    if decide (stExcGas.gas.gasRemaining < 0) then
                      outOfGasHalt stExcGas
                    else
                      .continue stExcGas

def childRun (host : Host) (fuel : Nat) (st : VmState) : Int × VmState :=
  match fuel with
  | 0 => (Excno.fatal.toInt, st)
  | fuel + 1 =>
      match childStep host st with
      | .continue st' =>
          childRun host fuel st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := tryCommit st'
            if ok then
              (exitCode, st'')
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              (~~~ Excno.cellOv.toInt, stFail)
          else
            (exitCode, st')

set_option maxHeartbeats 1000000 in
def runChildVm (host : Host) (parent : VmState) (mode : Nat) : VM VmState := do
  if mode ≥ 512 then
    throw .rangeChk

  -- Run on the provided parent state as the VM state.
  set (parent.consumeGas runvmGasPrice)

  -- Pop args in the same order as C++ `exec_runvm_common`.
  let sameC3 : Bool := (mode &&& 1) = 1
  let push0 : Bool := (mode &&& 2) = 2
  let withData : Bool := (mode &&& 4) = 4
  let returnGas : Bool := (mode &&& 8) = 8
  let loadC7 : Bool := (mode &&& 16) = 16
  let returnActions : Bool := (mode &&& 32) = 32
  let hasHardMax : Bool := (mode &&& 64) = 64
  let isolateGas : Bool := (mode &&& 128) = 128
  let hasRetVals : Bool := (mode &&& 256) = 256

  let gasMax0 : Int ←
    if hasHardMax then
      popGasRange
    else
      pure GasLimits.infty
  let gasLimit0 : Int ←
    if returnGas then
      popGasRange
    else
      pure GasLimits.infty
  let gasMax1 : Int := if hasHardMax then max gasMax0 gasLimit0 else gasLimit0

  let c7Opt : Option (Array Value) ←
    if loadC7 then
      some <$> VM.popTuple
    else
      pure none

  let dataOpt : Option Cell ←
    if withData then
      some <$> VM.popCell
    else
      pure none

  let retValsOpt : Option Nat ←
    if hasRetVals then
      some <$> VM.popNatUpTo (1 <<< 30)
    else
      pure none

  let codeSlice ← VM.popSlice

  let stBeforeSize ← get
  if stBeforeSize.stack.size = 0 then
    throw .stkUnd
  let stackSizeInt ← VM.popIntFinite
  if stackSizeInt < 0 then
    throw .rangeChk
  let stackSize : Nat := stackSizeInt.toNat
  let stAfterSize ← get
  if stackSize > stAfterSize.stack.size then
    throw .rangeChk

  let mut childStack : Array Value := Array.replicate stackSize .null
  for i in [0:stackSize] do
    let v ← VM.pop
    childStack := childStack.set! (stackSize - 1 - i) v

  modify fun st => st.consumeStackGas stackSize

  -- C++ `init_cregs`: `push_0` is honored only when `same_c3` is set.
  if sameC3 && push0 then
    childStack := childStack.push (.int (.num 0))

  let childCc : Continuation := .ordinary codeSlice (.quit 0) OrdCregs.empty OrdCdata.empty
  let childRegs0 : Regs := Regs.initial
  let childRegs1 : Regs := if sameC3 then { childRegs0 with c3 := childCc } else childRegs0
  let childRegs2 : Regs :=
    match c7Opt with
    | none => childRegs1
    | some t => { childRegs1 with c7 := t }
  let childRegs3 : Regs :=
    match dataOpt with
    | none => childRegs2
    | some c => { childRegs2 with c4 := c }

  let parentAfterPops ← get

  let parentRem : Int := parentAfterPops.gas.gasRemaining
  let gasMax : Int := min gasMax1 parentRem
  let gasLimit : Int := min gasLimit0 parentRem
  let childGas : GasLimits := GasLimits.ofLimits gasLimit gasMax 0

  let child : VmState :=
    { (VmState.initial codeSlice.cell) with
      stack := childStack
      regs := childRegs3
      cc := childCc
      gas := childGas
      loadedCells := if isolateGas then #[] else parentAfterPops.loadedCells
      chksgnCounter := if isolateGas then 0 else parentAfterPops.chksgnCounter
      maxDataDepth := parentAfterPops.maxDataDepth }

  let (childExit, childFinal) := childRun host childFuelDefault child
  let mut resCode : Int := ~~~ childExit

  let childConsumed : Int := childFinal.gas.gasConsumed
  let pay : Int := min childConsumed (childFinal.gas.gasLimit + 1)
  let mut parentAfter : VmState := parentAfterPops.consumeGas pay

  let depth := childFinal.stack.size
  let mut retCnt : Nat := 0
  if resCode = 0 ∨ resCode = 1 then
    match retValsOpt with
    | some n =>
        if depth ≥ n then
          retCnt := n
        else
          retCnt := 0
          resCode := ~~~ Excno.stkUnd.toInt
          parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num 0)) }
    | none =>
        retCnt := depth
  else
    retCnt := Nat.min depth 1

  -- C++ `restore_parent_vm`: charge stack gas for returned value count before pushes.
  parentAfter := parentAfter.consumeStackGas retCnt

  for i in List.range retCnt |>.reverse do
    let pos := depth - 1 - i
    parentAfter := { parentAfter with stack := parentAfter.stack.push (childFinal.stack[pos]!) }

  parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num resCode)) }

  if withData then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c4) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push .null }
  if returnActions then
    if childFinal.cstate.committed then
      parentAfter := { parentAfter with stack := parentAfter.stack.push (.cell childFinal.cstate.c5) }
    else
      parentAfter := { parentAfter with stack := parentAfter.stack.push .null }
  if returnGas then
    parentAfter := { parentAfter with stack := parentAfter.stack.push (.int (.num childConsumed)) }

  return parentAfter

-- Leaf module hook used by `TvmLean.Semantics.Exec.Flow`.
set_option maxHeartbeats 1000000 in
def execInstrFlowRunvm (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt (.runvm mode) =>
      let st ← get
      let st' ← runChildVm host st mode
      set st'
  | .contExt .runvmx =>
      let mode ← popNatUpToSigned 4095
      let st ← get
      let st' ← runChildVm host st mode
      set st'
  | _ =>
      next

end TvmLean
