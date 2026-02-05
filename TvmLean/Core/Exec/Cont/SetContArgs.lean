import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSetContArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setContArgs copy more =>
      -- Mirrors `SETCONTARGS` from `crypto/vm/contops.cpp` (exec_setcontargs + exec_setcontargs_common).
      if copy > 15 then
        throw .rangeChk
      if decide (more < -1 ∨ more > 14) then
        throw .rangeChk
      let copyN : Nat := copy
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
              if decide (0 ≤ cdata.nargs ∧ cdata.nargs < Int.ofNat copyN) then
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
                cdata := { cdata with nargs := cdata.nargs - Int.ofNat copyN }
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
              if decide (0 ≤ cdata.nargs ∧ cdata.nargs < Int.ofNat copyN) then
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
                cdata := { cdata with nargs := cdata.nargs - Int.ofNat copyN }
            if decide (more ≥ 0) then
              if decide (cdata.nargs > more) then
                cdata := { cdata with nargs := 0x40000000 }
              else if decide (cdata.nargs < 0) then
                cdata := { cdata with nargs := more }
            cont := .envelope ext cregs cdata
            VM.push (.cont cont)
        | _ =>
            throw .typeChk
  | _ => next

end TvmLean

