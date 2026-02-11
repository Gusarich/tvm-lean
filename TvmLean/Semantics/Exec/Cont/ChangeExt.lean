import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContChangeExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt op =>
      match op with
      | .pushCtrX =>
          VM.checkUnderflow 1
          let idx ← VM.popNatUpTo 16
          let st ← get
          match st.getCtr idx with
          | .ok v => VM.push v
          | .error e => throw e
      | .popCtrX =>
          VM.checkUnderflow 2
          let idx ← VM.popNatUpTo 16
          if idx = 6 || idx > 7 then
            throw .rangeChk
          let v ← VM.pop
          let st ← get
          match st.setCtr idx v with
          | .ok st' => set st'
          | .error e => throw e
      | .setContCtrX =>
          VM.checkUnderflow 3
          let idx ← VM.popNatUpTo 16
          if idx = 6 || idx > 7 then
            throw .rangeChk
          let cont ← VM.popCont
          let v ← VM.pop
          match cont.defineCtr idx v with
          | .ok cont' => VM.push (.cont cont')
          | .error e => throw e
      | .setContCtrMany mask =>
          if (mask &&& (1 <<< 6)) ≠ 0 then
            throw .rangeChk
          let cont ← VM.popCont
          let st ← get
          let mut cont' := cont
          for i in [0:8] do
            if (mask &&& (1 <<< i)) ≠ 0 then
              match st.getCtr i with
              | .ok v =>
                  match cont'.defineCtr i v with
                  | .ok k => cont' := k
                  | .error e => throw e
              | .error e => throw e
          VM.push (.cont cont')
      | .setContCtrManyX =>
          VM.checkUnderflow 2
          let mask ← VM.popNatUpTo 255
          if (mask &&& (1 <<< 6)) ≠ 0 then
            throw .rangeChk
          let cont ← VM.popCont
          let st ← get
          let mut cont' := cont
          for i in [0:8] do
            if (mask &&& (1 <<< i)) ≠ 0 then
              match st.getCtr i with
              | .ok v =>
                  match cont'.defineCtr i v with
                  | .ok k => cont' := k
                  | .error e => throw e
              | .error e => throw e
          VM.push (.cont cont')
      | .setRetCtr idx =>
          VM.checkUnderflow 1
          let v ← VM.pop
          let st ← get
          match st.regs.c0.defineCtr idx v with
          | .ok c0' =>
              set { st with regs := { st.regs with c0 := c0' } }
          | .error e => throw e
      | .setAltCtr idx =>
          VM.checkUnderflow 1
          let v ← VM.pop
          let st ← get
          match st.regs.c1.defineCtr idx v with
          | .ok c1' =>
              set { st with regs := { st.regs with c1 := c1' } }
          | .error e => throw e
      | .popSave idx =>
          VM.checkUnderflow 1
          let v ← VM.pop
          let st ← get
          match st.getCtr idx with
          | .error e => throw e
          | .ok oldVal =>
              match st.regs.c0.defineCtr idx oldVal with
              | .error e => throw e
              | .ok c0' =>
                  if idx = 0 then
                    -- Match C++ ordering: update c0 first, then set c0 := v.
                    let st1 : VmState := { st with regs := { st.regs with c0 := c0' } }
                    match st1.setCtr idx v with
                    | .ok st2 => set st2
                    | .error e => throw e
                  else
                    match st.setCtr idx v with
                    | .error e => throw e
                    | .ok st1 =>
                        set { st1 with regs := { st1.regs with c0 := c0' } }
      | .saveAltCtr idx =>
          let st ← get
          match st.getCtr idx with
          | .error e => throw e
          | .ok v =>
              match st.regs.c1.defineCtr idx v with
              | .ok c1' => set { st with regs := { st.regs with c1 := c1' } }
              | .error e => throw e
      | .saveBothCtr idx =>
          let st ← get
          match st.getCtr idx with
          | .error e => throw e
          | .ok v =>
              match st.regs.c0.defineCtr idx v with
              | .error e => throw e
              | .ok c0' =>
                  match st.regs.c1.defineCtr idx v with
                  | .error e => throw e
                  | .ok c1' =>
                      set { st with regs := { st.regs with c0 := c0', c1 := c1' } }
      | .setExitAlt =>
          let cont ← VM.popCont
          let st ← get
          let cont' := (cont.defineC0 st.regs.c0).defineC1 st.regs.c1
          set { st with regs := { st.regs with c1 := cont' } }
      | _ =>
          next
  | _ =>
      next

end TvmLean
