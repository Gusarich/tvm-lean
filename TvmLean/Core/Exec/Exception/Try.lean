import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionTry (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
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
  | .tryArgs params retVals =>
      let handler ← VM.popCont
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let codeAfter : Slice ←
        match st.cc with
        | .ordinary code _ _ _ => pure code
        | _ => throw .typeChk

      -- Mirrors `VmState::extract_cc(7, params, retvals)` in C++:
      --   - save current control regs (c0,c1,c2) into the continuation,
      --   - split the stack so that the TRY body sees only the top `params`,
      --   - when the continuation is later entered, keep only the top `retVals`.
      let oldC0 : Continuation := st.regs.c0
      let oldC1 : Continuation := st.regs.c1
      let oldC2 : Continuation := st.regs.c2
      let ccCregs : OrdCregs :=
        { OrdCregs.empty with c0 := some oldC0, c1 := some oldC1, c2 := some oldC2 }
      let depth : Nat := st.stack.size
      let split : Nat := depth - params
      let saved : Stack := st.stack.take split
      let args : Stack := st.stack.extract split depth
      let ccCdata : OrdCdata := { stack := saved, nargs := Int.ofNat retVals }
      let cc : Continuation := .ordinary codeAfter (.quit 0) ccCregs ccCdata

      -- Charge stack gas for the new stack depth (C++ `extract_cc` does this when splitting).
      let st := { st with stack := args }
      let st := st.consumeStackGas args.size

      -- Mirrors `force_cregs(handler_cont)->define_c2(old_c2); define_c0(cc);`
      let handler' : Continuation := (handler.defineC2 oldC2).defineC0 cc
      -- Mirrors `extract_cc` clearing `c1 := quit1` for the TRY body.
      set { st with regs := { st.regs with c0 := cc, c1 := .quit 1, c2 := handler' }, cc := cont }
  | _ => next

end TvmLean
