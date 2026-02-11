import TvmLean.Model
import TvmLean.Semantics.VM.Monad
import TvmLean.Semantics.VM.Ops.Stack
import TvmLean.Semantics.VM.Ops.Gas

namespace TvmLean

def VM.jump (cont : Continuation) (passArgs : Int := -1) : VM Unit := do
  -- Mirrors C++ `VmState::adjust_jump_cont(cont, pass_args)` stack handling.
  let st ← get
  let depth : Nat := st.stack.size
  if decide (passArgs ≥ 0) then
    let k : Nat := passArgs.toNat
    if k > depth then
      throw .stkUnd
  match cont with
  | .ordinary _ _ _ cdata
  | .envelope _ _ cdata =>
      if decide (0 ≤ cdata.nargs) then
        let nargs : Nat := cdata.nargs.toNat
        if nargs > depth then
          throw .stkUnd
        if decide (passArgs ≥ 0) then
          if cdata.nargs > passArgs then
            throw .stkUnd
      let mut copy : Int := cdata.nargs
      if decide (passArgs ≥ 0 ∧ copy < 0) then
        copy := passArgs
      if cdata.stack.isEmpty then
        if decide (copy ≥ 0) then
          let n : Nat := copy.toNat
          if n < depth then
            let newStack : Stack := st.stack.extract (depth - n) depth
            set { st with stack := newStack }
            modify fun st => st.consumeStackGas newStack.size
      else
        let copyN : Nat := if decide (copy ≥ 0) then copy.toNat else depth
        let argsStack : Stack := st.stack.extract (depth - copyN) depth
        let newStack : Stack := cdata.stack ++ argsStack
        set { st with stack := newStack }
        modify fun st => st.consumeStackGas newStack.size
  | _ =>
      if decide (passArgs ≥ 0) then
        let n : Nat := passArgs.toNat
        if n < depth then
          let newStack : Stack := st.stack.extract (depth - n) depth
          set { st with stack := newStack }
          modify fun st => st.consumeStackGas newStack.size
  modify fun st => { st with cc := cont }

def VM.callComputeStacks (stack captured : Stack) (nargs passArgs : Int) : VM (Stack × Stack × Bool) := do
  let depth : Nat := stack.size
  if decide (nargs > Int.ofNat depth) then
    throw .stkUnd
  if decide (passArgs ≥ 0 ∧ nargs > passArgs) then
    throw .stkUnd

  let mut copy : Int := nargs
  let mut skip : Int := 0
  if decide (passArgs ≥ 0) then
    if decide (copy ≥ 0) then
      skip := passArgs - copy
    else
      copy := passArgs

  let skipN : Nat := if decide (skip > 0) then skip.toNat else 0
  if captured.isEmpty then
    if decide (copy ≥ 0) then
      let n : Nat := copy.toNat
      if n > depth then
        throw .stkUnd
      let split : Nat := depth - n
      let afterCopy : Stack := stack.take split
      if skipN > afterCopy.size then
        throw .stkUnd
      let savedDepth : Nat := afterCopy.size - skipN
      let savedStack : Stack := afterCopy.take savedDepth
      let newStack : Stack := stack.extract split depth
      return (savedStack, newStack, true)
    else
      return (#[], stack, false)
  else
    if decide (copy < 0) then
      let newStack : Stack := captured ++ stack
      return (#[], newStack, true)
    else
      let n : Nat := copy.toNat
      if n > depth then
        throw .stkUnd
      let split : Nat := depth - n
      let afterCopy : Stack := stack.take split
      if skipN > afterCopy.size then
        throw .stkUnd
      let savedDepth : Nat := afterCopy.size - skipN
      let savedStack : Stack := afterCopy.take savedDepth
      let argsStack : Stack := stack.extract split depth
      let newStack : Stack := captured ++ argsStack
      return (savedStack, newStack, true)

def VM.call (cont : Continuation) (passArgs : Int := -1) (retArgs : Int := -1) : VM Unit := do
  let installReturnCont (frame : CallFrame) (k : Continuation) : VM Unit := do
    let st ← get
    let oldC0 := st.regs.c0
    let retCont :=
      match st.cc with
      | .ordinary code _ _ _ =>
          let cregsRet : OrdCregs := { OrdCregs.empty with c0 := some oldC0 }
          let cdataRet : OrdCdata := { stack := frame.savedStack, nargs := frame.retArgs }
          .ordinary code (.quit 0) cregsRet cdataRet
      | _ => .quit 0
    set { st with regs := { st.regs with c0 := retCont }, cc := k }

  let st ← get
  let depth : Nat := st.stack.size
  if decide (passArgs ≥ 0) then
    let n : Nat := passArgs.toNat
    if n > depth then
      throw .stkUnd

  match cont with
  | .ordinary code saved cregs cdata =>
      if cregs.c0.isSome then
        -- C++: call reduces to jump if callee already defines c0.
        VM.jump cont passArgs
      else
        let (savedStack, newStack, chargeStackGas) ← VM.callComputeStacks st.stack cdata.stack cdata.nargs passArgs
        set { st with stack := newStack }
        if chargeStackGas then
          modify fun st => st.consumeStackGas newStack.size
        let frame : CallFrame := { savedStack, retArgs := retArgs }
        let cont' : Continuation := .ordinary code saved cregs OrdCdata.empty
        installReturnCont frame cont'
  | .envelope ext cregs cdata =>
      if cregs.c0.isSome then
        VM.jump cont passArgs
      else
        let (savedStack, newStack, chargeStackGas) ← VM.callComputeStacks st.stack cdata.stack cdata.nargs passArgs
        set { st with stack := newStack }
        if chargeStackGas then
          modify fun st => st.consumeStackGas newStack.size
        let frame : CallFrame := { savedStack, retArgs := retArgs }
        let cont' : Continuation := .envelope ext cregs OrdCdata.empty
        installReturnCont frame cont'
  | _ =>
      let (savedStack, newStack, chargeStackGas) :=
        if decide (passArgs ≥ 0) then
          let n : Nat := passArgs.toNat
          let split : Nat := depth - n
          (st.stack.take split, st.stack.extract split depth, true)
        else
          (#[], st.stack, false)
      set { st with stack := newStack }
      if chargeStackGas then
        modify fun st => st.consumeStackGas newStack.size
      let frame : CallFrame := { savedStack, retArgs := retArgs }
      installReturnCont frame cont

def VM.ret (passArgs : Int := -1) : VM Unit := do
  let st ← get
  let cont := st.regs.c0
  set { st with regs := { st.regs with c0 := .quit 0 } }
  VM.jump cont passArgs

def VM.retAlt (passArgs : Int := -1) : VM Unit := do
  let st ← get
  let cont := st.regs.c1
  set { st with regs := { st.regs with c1 := .quit 1 } }
  VM.jump cont passArgs

end TvmLean
