import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSetNumVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setNumVarArgs =>
      -- Mirrors `SETNUMVARARGS` from `crypto/vm/contops.cpp` (exec_setnum_varargs + exec_setcontargs_common copy=0).
      VM.checkUnderflow 2
      let moreVal ← VM.popInt
      let more : Int ←
        match moreVal with
        | .nan => throw .rangeChk
        | .num n => pure n
      if decide (more < -1 ∨ more > 255) then
        throw .rangeChk
      let cont ← VM.popCont
      if more = -1 then
        -- copy=0, more=-1: do not force cdata / wrap the continuation.
        VM.push (.cont cont)
      else
        let mut cont := cont.forceCdata
        match cont with
        | .ordinary code saved cregs cdata =>
            let mut cdata := cdata
            if decide (cdata.nargs > more) then
              cdata := { cdata with nargs := 0x40000000 }
            else if decide (cdata.nargs < 0) then
              cdata := { cdata with nargs := more }
            cont := .ordinary code saved cregs cdata
            VM.push (.cont cont)
        | .envelope ext cregs cdata =>
            let mut cdata := cdata
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
