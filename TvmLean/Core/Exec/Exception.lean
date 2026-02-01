import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrException (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throw exc =>
      modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
  | .throwIf exc =>
      if (← VM.popBool) then
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
      else
        pure ()
  | .throwIfNot exc =>
      let flag ← VM.popBool
      if flag then
        pure ()
      else
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
  | .throwArg exc =>
      let arg ← VM.pop
      modify fun st => (st.throwExceptionArg exc arg).consumeGas exceptionGasPrice
  | .throwArgIf exc =>
      let cond ← VM.popBool
      if cond then
        let arg ← VM.pop
        modify fun st => (st.throwExceptionArg exc arg).consumeGas exceptionGasPrice
      else
        let _ ← VM.pop
        pure ()
  | .throwArgIfNot exc =>
      let cond ← VM.popBool
      if cond then
        let _ ← VM.pop
        pure ()
      else
        let arg ← VM.pop
        modify fun st => (st.throwExceptionArg exc arg).consumeGas exceptionGasPrice
  | .throwAny hasParam hasCond throwCond =>
      let flag ←
        if hasCond then
          VM.popBool
        else
          pure throwCond
      let excnoNat ← VM.popNatUpTo 0xffff
      let excno : Int := Int.ofNat excnoNat
      if flag != throwCond then
        if hasParam then
          let _ ← VM.pop
          pure ()
        else
          pure ()
      else
        if hasParam then
          let arg ← VM.pop
          modify fun st => (st.throwExceptionArg excno arg).consumeGas exceptionGasPrice
        else
          modify fun st => (st.throwException excno).consumeGas exceptionGasPrice
  | .try_ =>
      let handler ← VM.popCont
      let cont ← VM.popCont
      let st ← get
      let codeAfter : Slice ←
        match st.cc with
        | .ordinary code _ _ _ => pure code
        | _ => throw .typeChk
      -- Mirrors `VmState::extract_cc(7)` in C++: capture current control regs (c0,c1,c2) inside the
      -- continuation so that they are restored when it is entered after a successful TRY.
      let oldC0 : Continuation := st.regs.c0
      let oldC1 : Continuation := st.regs.c1
      let oldC2 : Continuation := st.regs.c2
      let ccCregs : OrdCregs :=
        { OrdCregs.empty with c0 := some oldC0, c1 := some oldC1, c2 := some oldC2 }
      let cc : Continuation := .ordinary codeAfter (.quit 0) ccCregs OrdCdata.empty
      -- Mirrors `force_cregs(handler_cont)->define_c2(old_c2); define_c0(cc);`
      let handler' : Continuation := (handler.defineC2 oldC2).defineC0 cc
      -- Mirrors `extract_cc` clearing `c1 := quit1` for the TRY body.
      set { st with regs := { st.regs with c0 := cc, c1 := .quit 1, c2 := handler' }, cc := cont }
  | _ => next

end TvmLean
