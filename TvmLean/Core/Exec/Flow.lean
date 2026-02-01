import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlow (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setcp cp =>
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        throw .invOpcode
  | .ifret =>
      if (← VM.popBool) then
        VM.ret
      else
        pure ()
  | .ifnotret =>
      if !(← VM.popBool) then
        VM.ret
      else
        pure ()
  | .if_ =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont
      else
        pure ()
  | .ifnot =>
      let cont ← VM.popCont
      if !(← VM.popBool) then
        modify fun st => st.callTo cont
      else
        pure ()
  | .pushSliceConst s =>
      VM.push (.slice s)
  | .pushCont code =>
      VM.push (.cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty))
  | .pushRef c =>
      -- Matches C++ `exec_push_ref` (cellops.cpp), mode 0: push cell without loading.
      VM.push (.cell c)
  | .pushRefSlice c =>
      -- Matches C++ `exec_push_ref` (cellops.cpp), mode 1: load cell slice (charges cell load).
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
  | .pushRefCont c =>
      modify fun st => st.registerCellLoad c
      VM.push (.cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty))
  | .execute =>
      let cont ← VM.popCont
      modify fun st => st.callTo cont
  | .jmpx =>
      let cont ← VM.popCont
      modify fun st => st.jumpTo cont
  | .callxArgs params retVals =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let split : Nat := depth - params
      let saved : Stack := st.stack.take split
      let args : Stack := st.stack.extract split depth
      let frame : CallFrame := { savedStack := saved, retArgs := retVals }
      set { st with stack := args }
      -- C++ `call(..., pass_args=params, ...)` charges stack gas for the new stack depth.
      modify fun st => st.consumeStackGas args.size
      modify fun st => st.callToWithFrame frame cont
  | .jmpxArgs params =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let start : Nat := depth - params
      let args : Stack := st.stack.extract start depth
      set { st with stack := args }
      -- C++ `jump(..., pass_args=params)` charges stack gas for the new stack depth.
      modify fun st => st.consumeStackGas args.size
      modify fun st => st.jumpTo cont
  | .ret =>
      VM.ret
  | .retAlt =>
      VM.retAlt
  | .retBool =>
      if (← VM.popBool) then
        VM.ret
      else
        VM.retAlt
  | .retArgs n =>
      VM.ret (Int.ofNat n)
  | .ifjmp =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.jumpTo cont
      else
        pure ()
  | .ifnotjmp =>
      let cont ← VM.popCont
      if !(← VM.popBool) then
        modify fun st => st.jumpTo cont
      else
        pure ()
  | .ifelse =>
      let cont0 ← VM.popCont
      let cont1 ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont1
      else
        modify fun st => st.callTo cont0
  | .ifref code =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifnotref code =>
      if !(← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifjmpref code =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.jumpTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifnotjmpref code =>
      if !(← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.jumpTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifrefElse code =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        modify fun st => st.callTo cont
  | .ifelseRef code =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont
      else
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .ifrefElseRef t f =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad t.cell
        modify fun st => st.callTo (.ordinary t (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        modify fun st => st.registerCellLoad f.cell
        modify fun st => st.callTo (.ordinary f (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .callRef code =>
      modify fun st => st.registerCellLoad code.cell
      modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .callDict idx =>
      VM.pushSmallInt (Int.ofNat idx)
      modify fun st => st.callTo st.regs.c3
  | .prepareDict idx =>
      -- Matches C++ `exec_preparedict` (contops.cpp).
      VM.pushSmallInt (Int.ofNat idx)
      let st ← get
      VM.push (.cont st.regs.c3)
  | .until =>
      -- Stack effect: ... body -- ...
      -- Control flow: execute `body`; if it returns `true` then continue, otherwise repeat.
      let body ← VM.popCont
      let st ← get
      let after :=
        match st.cc with
        | .ordinary rest _ _ _ => .ordinary rest st.regs.c0 OrdCregs.empty OrdCdata.empty
        | _ => st.cc
      -- C++ `VmState::until`: only installs the loop continuation into `c0` if `body` doesn't already have `c0`.
      if body.hasC0 then
        set { st with cc := body }
      else
        set { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
  | .while_ =>
      -- Stack effect: ... cond body -- ...
      -- Control flow: execute `cond`; if true then execute `body` and repeat.
      let body ← VM.popCont
      let cond ← VM.popCont
      let st ← get
      -- Capture the "after" continuation as the rest of the current code,
      -- but remember the current return continuation in `savedC0` so we can restore it when the loop terminates.
      let after :=
        match st.cc with
        | .ordinary rest _ _ _ => .ordinary rest st.regs.c0 OrdCregs.empty OrdCdata.empty
        | _ => st.cc
      set { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | .blkdrop2 x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let keepBottom : Nat := st.stack.size - total
        let bottom := st.stack.take keepBottom
        let top := st.stack.extract (keepBottom + x) st.stack.size
        modify fun st => { st with stack := bottom ++ top }
      else
        throw .stkUnd
  | .blkdrop n =>
      let st ← get
      if n ≤ st.stack.size then
        let keep : Nat := st.stack.size - n
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | .drop2 =>
      let st ← get
      if 2 ≤ st.stack.size then
        let keep : Nat := st.stack.size - 2
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | _ => next

end TvmLean
