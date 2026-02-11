import TvmLean.Semantics.Exec.Common

namespace TvmLean

def VmState.c1Envelope (st : VmState) (cont : Continuation) (save : Bool := true) : VmState × Continuation :=
  let cont' :=
    if save then
      (cont.defineC1 st.regs.c1).defineC0 st.regs.c0
    else
      cont
  ({ st with regs := { st.regs with c1 := cont' } }, cont')

def VmState.c1SaveSet (st : VmState) (save : Bool := true) : VmState :=
  let c0' := if save then st.regs.c0.defineC1 st.regs.c1 else st.regs.c0
  { st with regs := { st.regs with c0 := c0', c1 := c0' } }

def popSmallintRepeatCount : VM Int := do
  let i ← VM.popInt
  match i with
  | .nan =>
      throw .rangeChk
  | .num n =>
      if n < -0x80000000 ∨ n > 0x7fffffff then
        throw .rangeChk
      else
        return n

set_option maxHeartbeats 1000000 in
def execInstrFlowLoopExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt op =>
      match op with
      | .repeat brk =>
          VM.checkUnderflow 2
          let body ← VM.popCont
          let c ← popSmallintRepeatCount
          if c ≤ 0 then
            pure ()
          else
            let afterRaw ←
              if brk then
                -- Match C++ `exec_repeat`: `extract_cc(1)` must happen before `c1_envelope_if`.
                VM.extractCc 1
              else
                let st ← get
                pure <|
                  match st.cc with
                  | .ordinary rest _ cregs cdata => .ordinary rest st.regs.c0 cregs cdata
                  | _ => st.cc
            let st ← get
            let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
            set { st' with cc := .repeatBody body after c.toNat }
      | .repeatEnd brk =>
          VM.checkUnderflow 1
          let c ← popSmallintRepeatCount
          if c ≤ 0 then
            VM.ret
          else
            -- Match C++ `exec_repeat_end`: `body := extract_cc(0)` before `repeat`.
            let body ← VM.extractCc 0
            let st ← get
            let afterRaw := st.regs.c0
            let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
            set { st' with cc := .repeatBody body after c.toNat }
      | .until brk =>
          VM.checkUnderflow 1
          let body ← VM.popCont
          -- Match C++ `exec_until`: `after := extract_cc(1)` before optional c1 envelope.
          let afterRaw ← VM.extractCc 1
          let st ← get
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          if body.hasC0 then
            set { st' with cc := body }
          else
            set { st' with regs := { st'.regs with c0 := .untilBody body after }, cc := body }
      | .untilEnd brk =>
          -- Match C++ `exec_until_end`: `body := extract_cc(0)` (no save_cr side effects).
          let body ← VM.extractCc 0
          let st ← get
          let afterRaw := st.regs.c0
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          if body.hasC0 then
            set { st' with cc := body }
          else
            set { st' with regs := { st'.regs with c0 := .untilBody body after }, cc := body }
      | .while brk =>
          VM.checkUnderflow 2
          let body ← VM.popCont
          let cond ← VM.popCont
          -- Match C++ `exec_while`: `after := extract_cc(1)` first.
          let afterRaw ← VM.extractCc 1
          let st ← get
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          -- Match C++ `VmState::loop_while`: install loop-cont in c0 only when `cond` lacks c0.
          if cond.hasC0 then
            set { st' with cc := cond }
          else
            set { st' with regs := { st'.regs with c0 := .whileCond cond body after }, cc := cond }
      | .whileEnd brk =>
          VM.checkUnderflow 1
          let cond ← VM.popCont
          -- Match C++ `exec_while_end`: `body := extract_cc(0)`.
          let body ← VM.extractCc 0
          let st ← get
          let afterRaw := st.regs.c0
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          if cond.hasC0 then
            set { st' with cc := cond }
          else
            set { st' with regs := { st'.regs with c0 := .whileCond cond body after }, cc := cond }
      | .again brk =>
          if brk then
            -- Match C++ `exec_again`: perform `extract_cc(3)` before `pop_cont()`.
            let cc ← VM.extractCc 3
            modify fun st => { st with regs := { st.regs with c1 := cc } }
          VM.checkUnderflow 1
          let body ← VM.popCont
          modify fun st => { st with cc := .againBody body }
      | .againEnd brk =>
          -- Match C++ `exec_again_end`: optional `c1_save_set()` before `extract_cc(0)`,
          -- then `again(extracted_body)`.
          if brk then
            modify fun st => st.c1SaveSet
          let body ← VM.extractCc 0
          modify fun st => { st with cc := .againBody body }
      | .jmpDict idx =>
          VM.pushSmallInt (Int.ofNat idx)
          let st ← get
          VM.jump st.regs.c3
      | _ =>
          next
  | _ =>
      next

end TvmLean
