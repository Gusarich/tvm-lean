import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCont (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .pushCtr idx =>
      let st ← get
      match st.getCtr idx with
      | .ok v => VM.push v
      | .error e => throw e
  | .popCtr idx =>
      let v ← VM.pop
      let st ← get
      match st.setCtr idx v with
      | .ok st' => set st'
      | .error e => throw e
  | .setContCtr idx =>
      -- Mirrors `SETCONTCTR c<idx>` from `crypto/vm/contops.cpp` (`exec_setcont_ctr`):
      -- define `c<idx>` inside a continuation popped from the stack (wrapping with an envelope if needed).
      let cont ← VM.popCont
      let v ← VM.pop
      let cont ←
        match cont.defineCtr idx v with
        | .ok k => pure k
        | .error e => throw e
      VM.push (.cont cont)
  | .setContVarArgs =>
      -- Mirrors `SETCONTVARARGS` from `crypto/vm/contops.cpp` (exec_setcont_varargs + exec_setcontargs_common).
      -- Stack effect: ... <args...> cont copy more -- ... cont
      let more ← VM.popIntFinite
      if decide (more < -1 ∨ more > 255) then
        throw .rangeChk
      let copy ← VM.popIntFinite
      if decide (copy < 0 ∨ copy > 255) then
        throw .rangeChk
      let copyN : Nat := copy.toNat
      let st ← get
      if copyN + 1 > st.stack.size then
        throw .stkUnd
      let cont ← VM.popCont
      -- C++: if copy==0 and more==-1, do not force cdata / wrap the continuation.
      if copyN = 0 ∧ more = -1 then
        VM.push (.cont cont)
      else
        let mut cont := cont.forceCdata
        match cont with
        | .ordinary code saved cregs cdata =>
            let mut cdata := cdata
            if copyN > 0 then
              if decide (0 ≤ cdata.nargs ∧ cdata.nargs < copy) then
                throw .stkOv
              let st0 ← get
              let depth : Nat := st0.stack.size
              let start : Nat := depth - copyN
              let captured : Array Value := st0.stack.extract start depth
              let remaining : Stack := st0.stack.take start
              set { st0 with stack := remaining }
              cdata := { cdata with stack := cdata.stack ++ captured }
              -- C++ charges stack gas based on the closure stack depth.
              modify fun st => st.consumeStackGas cdata.stack.size
              if decide (0 ≤ cdata.nargs) then
                cdata := { cdata with nargs := cdata.nargs - copy }
            if decide (more ≥ 0) then
              if decide (cdata.nargs > more) then
                cdata := { cdata with nargs := 0x40000000 }
              else if decide (cdata.nargs < 0) then
                cdata := { cdata with nargs := more }
            cont := .ordinary code saved cregs cdata
            VM.push (.cont cont)
        | .envelope ext cregs cdata =>
            let mut cdata := cdata
            if copyN > 0 then
              if decide (0 ≤ cdata.nargs ∧ cdata.nargs < copy) then
                throw .stkOv
              let st0 ← get
              let depth : Nat := st0.stack.size
              let start : Nat := depth - copyN
              let captured : Array Value := st0.stack.extract start depth
              let remaining : Stack := st0.stack.take start
              set { st0 with stack := remaining }
              cdata := { cdata with stack := cdata.stack ++ captured }
              modify fun st => st.consumeStackGas cdata.stack.size
              if decide (0 ≤ cdata.nargs) then
                cdata := { cdata with nargs := cdata.nargs - copy }
            if decide (more ≥ 0) then
              if decide (cdata.nargs > more) then
                cdata := { cdata with nargs := 0x40000000 }
              else if decide (cdata.nargs < 0) then
                cdata := { cdata with nargs := more }
            cont := .envelope ext cregs cdata
            VM.push (.cont cont)
        | _ =>
            throw .typeChk
  | .saveCtr _idx =>
      -- Mirrors `SAVECTR c<idx>` from `crypto/vm/contops.cpp` (`exec_save_ctr`):
      -- define `c<idx>` inside the current return continuation `c0`.
      --
      let st ← get
      let v : Value ←
        match st.getCtr _idx with
        | .ok v => pure v
        | .error e => throw e
      let c0 ←
        match st.regs.c0.defineCtr _idx v with
        | .ok k => pure k
        | .error e => throw e
      set { st with regs := { st.regs with c0 := c0 } }
  | .sameAlt =>
      modify fun st => { st with regs := { st.regs with c1 := st.regs.c0 } }
  | .sameAltSave =>
      -- Mirrors `SAMEALTSAVE` from `crypto/vm/contops.cpp` (`exec_samealt(save=true)`):
      -- define `c1` inside `c0` (if absent), then set `c1 := c0`.
      let st ← get
      let c1Old : Continuation := st.regs.c1
      let c0' : Continuation := st.regs.c0.defineC1 c1Old
      set { st with regs := { st.regs with c0 := c0', c1 := c0' } }
  | .boolAnd =>
      -- Mirrors C++ `BOOLAND` (`exec_compos` with mask=1).
      let val ← VM.popCont
      let cont ← VM.popCont
      VM.push (.cont (cont.defineC0 val))
  | .boolOr =>
      -- Mirrors C++ `BOOLOR` (`exec_compos` with mask=2).
      let val ← VM.popCont
      let cont ← VM.popCont
      VM.push (.cont (cont.defineC1 val))
  | .composBoth =>
      -- Mirrors C++ `COMPOSBOTH` (`exec_compos` with mask=3).
      let val ← VM.popCont
      let cont ← VM.popCont
      let cont := cont.defineC0 val
      VM.push (.cont (cont.defineC1 val))
  | _ => next

end TvmLean
