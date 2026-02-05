import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Stack
import TvmLean.Core.Exec.Cont
import TvmLean.Core.Exec.Cell
import TvmLean.Core.Exec.Flow.Setcp
import TvmLean.Core.Exec.Flow.Ifret
import TvmLean.Core.Exec.Flow.Ifnotret
import TvmLean.Core.Exec.Flow.IfretAlt
import TvmLean.Core.Exec.Flow.If
import TvmLean.Core.Exec.Flow.Ifnot
import TvmLean.Core.Exec.Flow.PushSliceConst
import TvmLean.Core.Exec.Flow.PushCont
import TvmLean.Core.Exec.Flow.PushRef
import TvmLean.Core.Exec.Flow.PushRefSlice
import TvmLean.Core.Exec.Flow.PushRefCont
import TvmLean.Core.Exec.Flow.Execute
import TvmLean.Core.Exec.Flow.Jmpx
import TvmLean.Core.Exec.Flow.CallxArgs
import TvmLean.Core.Exec.Flow.JmpxArgs
import TvmLean.Core.Exec.Flow.Callcc
import TvmLean.Core.Exec.Flow.CallxVarArgs
import TvmLean.Core.Exec.Flow.Ret
import TvmLean.Core.Exec.Flow.RetAlt
import TvmLean.Core.Exec.Flow.RetBool
import TvmLean.Core.Exec.Flow.RetArgs
import TvmLean.Core.Exec.Flow.RetVarArgs
import TvmLean.Core.Exec.Flow.RetData
import TvmLean.Core.Exec.Flow.JmpxVarArgs
import TvmLean.Core.Exec.Flow.JmpxData
import TvmLean.Core.Exec.Flow.Ifjmp
import TvmLean.Core.Exec.Flow.Ifnotjmp
import TvmLean.Core.Exec.Flow.Ifelse
import TvmLean.Core.Exec.Flow.Ifref
import TvmLean.Core.Exec.Flow.Ifnotref
import TvmLean.Core.Exec.Flow.Ifjmpref
import TvmLean.Core.Exec.Flow.Ifnotjmpref
import TvmLean.Core.Exec.Flow.IfrefElse
import TvmLean.Core.Exec.Flow.IfelseRef
import TvmLean.Core.Exec.Flow.IfrefElseRef
import TvmLean.Core.Exec.Flow.IfBitJmp
import TvmLean.Core.Exec.Flow.CallRef
import TvmLean.Core.Exec.Flow.JmpRef
import TvmLean.Core.Exec.Flow.CallDict
import TvmLean.Core.Exec.Flow.PrepareDict
import TvmLean.Core.Exec.Flow.Until
import TvmLean.Core.Exec.Flow.While
import TvmLean.Core.Exec.Flow.LoopExt
import TvmLean.Core.Exec.Flow.Blkdrop2
import TvmLean.Core.Exec.Flow.Blkdrop
import TvmLean.Core.Exec.Flow.Drop2
import TvmLean.Core.Exec.Arith
import TvmLean.Core.Exec.Tuple
import TvmLean.Core.Exec.CellOp
import TvmLean.Core.Exec.TonEnv
import TvmLean.Core.Exec.Crypto
import TvmLean.Core.Exec.Msg
import TvmLean.Core.Exec.Misc
import TvmLean.Core.Exec.Debug
import TvmLean.Core.Exec.Exception
import TvmLean.Core.Exec.Dict

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

set_option maxHeartbeats 1000000 in
def execInstrFlowChildNoRunvm (i : Instr) (next : VM Unit) : VM Unit :=
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
def execInstrChildNoRunvm (i : Instr) : VM Unit :=
  execInstrStack i <|
    execInstrCont i <|
      execInstrCell i <|
        execInstrFlowChildNoRunvm i <|
          execInstrArith i <|
            execInstrTuple i <|
              execInstrCellOp i <|
                execInstrTonEnv i <|
                  execInstrCrypto i <|
                    execInstrMsg i <|
                      execInstrMisc i <|
                      execInstrDebug i <|
                      execInstrException i <|
                        execInstrDict i <|
                          throw .invOpcode

def outOfGasHalt (st : VmState) : ChildStepResult :=
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  ChildStepResult.halt Excno.outOfGas.toInt st'

def childStep (st : VmState) : ChildStepResult :=
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
            let st0 := st.throwException e.toInt
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
              let (res, st1) := (execInstrChildNoRunvm instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    outOfGasHalt st1
                  else
                    .continue st1
              | .error e =>
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    outOfGasHalt stExcGas
                  else
                    .continue stExcGas

def childRun (fuel : Nat) (st : VmState) : Int × VmState :=
  match fuel with
  | 0 => (Excno.fatal.toInt, st)
  | fuel + 1 =>
      match childStep st with
      | .continue st' =>
          childRun fuel st'
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
def runChildVm (parent : VmState) (mode : Nat) : VM VmState := do
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

  if push0 && !sameC3 then
    throw .rangeChk

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

  if push0 then
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

  let (childExit, childFinal) := childRun childFuelDefault child
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

-- Leaf module hook used by `TvmLean.Core.Exec.Flow`.
set_option maxHeartbeats 1000000 in
def execInstrFlowRunvm (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt (.runvm mode) =>
      let st ← get
      let st' ← runChildVm st mode
      set st'
  | .contExt .runvmx =>
      let mode ← popNatUpToSigned 4095
      let st ← get
      let st' ← runChildVm st mode
      set st'
  | _ =>
      next

end TvmLean
