import TvmLean.Core.Exec.Common

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
  let n ← VM.popIntFinite
  if n < -0x80000000 ∨ n > 0x7fffffff then
    throw .rangeChk
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
            let st ← get
            let afterRaw :=
              match st.cc with
              | .ordinary rest _ cregs cdata => .ordinary rest st.regs.c0 cregs cdata
              | _ => st.cc
            let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
            set { st' with cc := .repeatBody body after c.toNat }
      | .repeatEnd brk =>
          VM.checkUnderflow 1
          let c ← popSmallintRepeatCount
          if c ≤ 0 then
            VM.ret
          else
            let st ← get
            let body := st.cc
            let afterRaw := st.regs.c0
            let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
            set { st' with cc := .repeatBody body after c.toNat }
      | .until brk =>
          VM.checkUnderflow 1
          let body ← VM.popCont
          let st ← get
          let afterRaw :=
            match st.cc with
            | .ordinary rest _ cregs cdata => .ordinary rest st.regs.c0 cregs cdata
            | _ => st.cc
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          if body.hasC0 then
            set { st' with cc := body }
          else
            set { st' with regs := { st'.regs with c0 := .untilBody body after }, cc := body }
      | .untilEnd brk =>
          let st ← get
          let body := st.cc
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
          let st ← get
          let afterRaw :=
            match st.cc with
            | .ordinary rest _ cregs cdata => .ordinary rest st.regs.c0 cregs cdata
            | _ => st.cc
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          set { st' with regs := { st'.regs with c0 := .whileCond cond body after }, cc := cond }
      | .whileEnd brk =>
          VM.checkUnderflow 1
          let cond ← VM.popCont
          let st ← get
          let body := st.cc
          let afterRaw := st.regs.c0
          let (st', after) := if brk then st.c1Envelope afterRaw else (st, afterRaw)
          set { st' with regs := { st'.regs with c0 := .whileCond cond body after }, cc := cond }
      | .again brk =>
          VM.checkUnderflow 1
          let body ← VM.popCont
          let st ← get
          if brk then
            let after :=
              match st.cc with
              | .ordinary rest _ cregs cdata => .ordinary rest st.regs.c0 cregs cdata
              | _ => st.cc
            set { st with regs := { st.regs with c1 := after }, cc := .againBody body }
          else
            set { st with cc := .againBody body }
      | .againEnd brk =>
          let st ← get
          let st := if brk then st.c1SaveSet else st
          set { st with cc := .againBody st.cc }
      | .jmpDict idx =>
          VM.pushSmallInt (Int.ofNat idx)
          let st ← get
          VM.jump st.regs.c3
      | _ =>
          next
  | _ =>
      next

end TvmLean
