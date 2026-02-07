import TvmLean.Model
import TvmLean.Semantics.VM.Monad

namespace TvmLean

def VM.push (v : Value) : VM Unit := do
  modify fun st => { st with stack := st.stack.push v }

def VM.pop : VM Value := do
  let st ← get
  if h : 0 < st.stack.size then
    let v := st.stack.back (h := h)
    modify fun st => { st with stack := st.stack.pop }
    return v
  else
    throw .stkUnd

def VM.fetch (idxFromTop : Nat) : VM Value := do
  let st ← get
  if _h : idxFromTop < st.stack.size then
    let pos := st.stack.size - 1 - idxFromTop
    return st.stack[pos]!
  else
    throw .stkUnd

def VM.swap (iFromTop jFromTop : Nat) : VM Unit := do
  let st ← get
  let need := Nat.max iFromTop jFromTop
  if _h : need < st.stack.size then
    let pi := st.stack.size - 1 - iFromTop
    let pj := st.stack.size - 1 - jFromTop
    let vi := st.stack[pi]!
    let vj := st.stack[pj]!
    modify fun st =>
      let s := st.stack
      { st with stack := (s.set! pi vj).set! pj vi }
  else
    throw .stkUnd

def VM.popInt : VM IntVal := do
  let v ← VM.pop
  match v with
  | .int i => return i
  | _ => throw .typeChk

def VM.popCont : VM Continuation := do
  let v ← VM.pop
  match v with
  | .cont k => return k
  | _ => throw .typeChk

def VM.popBool : VM Bool := do
  let i ← VM.popInt
  match i.toBool? with
  | .ok b => return b
  | .error e => throw e

def VM.pushIntQuiet (i : IntVal) (quiet : Bool) : VM Unit := do
  match i with
  | .nan =>
      if quiet then
        VM.push (.int .nan)
      else
        throw .intOv
  | .num _ =>
      if i.signedFits257 then
        VM.push (.int i)
      else
        if quiet then
          VM.push (.int .nan)
        else
          throw .intOv

def VM.pushSmallInt (n : Int) : VM Unit := do
  -- Always fits 257-bit in practice for our uses.
  VM.push (.int (.num n))

def VM.popIntFinite : VM Int := do
  let v ← VM.popInt
  match v with
  | .nan => throw .intOv
  | .num n => return n

def VM.popNatUpTo (max : Nat) : VM Nat := do
  let v ← VM.popInt
  match v with
  | .nan => throw .rangeChk
  | .num n =>
      if n < 0 then
        throw .rangeChk
      let u := n.toNat
      if u > max then
        throw .rangeChk
      return u

end TvmLean
