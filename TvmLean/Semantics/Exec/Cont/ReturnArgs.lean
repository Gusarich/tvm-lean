import TvmLean.Semantics.Exec.Common

namespace TvmLean

def VM.returnArgsCommon (count : Nat) : VM Unit := do
  if count > 255 then
    throw .rangeChk
  let st ← get
  if count > st.stack.size then
    throw .stkUnd
  let depth : Nat := st.stack.size
  if depth = count then
    pure ()
  else
    let copy : Nat := depth - count
    let bottom : Stack := st.stack.take copy
    let keep : Stack := st.stack.extract copy depth
    -- Install `keep` as the new current stack.
    set { st with stack := keep }

    -- Update `c0` closure stack with the removed `bottom` elements.
    let mut c0 := st.regs.c0.forceCdata
    match c0 with
    | .ordinary code saved cregs cdata =>
        let mut cdata := cdata
        if decide (0 ≤ cdata.nargs) then
          if decide (cdata.nargs < Int.ofNat copy) then
            throw .stkOv
        cdata := { cdata with stack := cdata.stack ++ bottom }
        modify fun st => st.consumeStackGas cdata.stack.size
        if decide (0 ≤ cdata.nargs) then
          cdata := { cdata with nargs := cdata.nargs - Int.ofNat copy }
        c0 := .ordinary code saved cregs cdata
    | .envelope ext cregs cdata =>
        let mut cdata := cdata
        if decide (0 ≤ cdata.nargs) then
          if decide (cdata.nargs < Int.ofNat copy) then
            throw .stkOv
        cdata := { cdata with stack := cdata.stack ++ bottom }
        modify fun st => st.consumeStackGas cdata.stack.size
        if decide (0 ≤ cdata.nargs) then
          cdata := { cdata with nargs := cdata.nargs - Int.ofNat copy }
        c0 := .envelope ext cregs cdata
    | _ =>
        throw .typeChk
    modify fun st => { st with regs := { st.regs with c0 := c0 } }

set_option maxHeartbeats 1000000 in
def execInstrContReturnArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .returnArgs count =>
      -- C++ helper canonicalizes immediate payload as `args & 15`.
      let params : Nat := count &&& 0xf
      VM.returnArgsCommon params
  | .returnVarArgs =>
      let n ← VM.popNatUpTo 255
      VM.returnArgsCommon n
  | _ => next

end TvmLean
