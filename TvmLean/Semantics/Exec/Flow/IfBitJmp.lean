import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def intBit (n : Int) (i : Nat) : Bool :=
  if decide (n ≥ 0) then
    (Int.toNat n).testBit i
  else
    let m : Int := (2 : Int) ^ (i + 1)
    let r : Int := Int.emod n m
    (Int.toNat r).testBit i

private def intValBit? (x : IntVal) (i : Nat) : Except Excno Bool :=
  match x with
  | .nan => .error .intOv
  | .num n => .ok (intBit n i)

private def popIntFiniteKeepAndBit (idx : Nat) : VM Bool := do
  let x ← VM.popIntFinite
  let bit := intBit x idx
  VM.push (.int (.num x))
  pure bit

set_option maxHeartbeats 1000000 in
def execInstrFlowIfBitJmp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt (.ifbitjmp idx) =>
      VM.checkUnderflow 2
      let body ← VM.popCont
      if (← popIntFiniteKeepAndBit idx) then
        VM.jump body
      else
        pure ()
  | .contExt (.ifnbitjmp idx) =>
      VM.checkUnderflow 2
      let body ← VM.popCont
      if !(← popIntFiniteKeepAndBit idx) then
        VM.jump body
      else
        pure ()
  | .contExt (.ifbitjmpref idx code) =>
      let x ← VM.fetch 0
      match x with
      | .int v =>
          match intValBit? v idx with
          | .ok true =>
              VM.registerCellLoad code.cell
              VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
          | .ok false => pure ()
          | .error e => throw e
      | _ => throw .typeChk
  | .contExt (.ifnbitjmpref idx code) =>
      let x ← VM.fetch 0
      match x with
      | .int v =>
          match intValBit? v idx with
          | .ok true => pure ()
          | .ok false =>
              VM.registerCellLoad code.cell
              VM.jump (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
          | .error e => throw e
      | _ => throw .typeChk
  | _ => next

end TvmLean
