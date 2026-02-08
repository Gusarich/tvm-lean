import TvmLean.Semantics.Exec.Common

namespace TvmLean

def signedBitsizeTvm (n : Int) : Nat :=
  if n = 0 then
    0
  else if n > 0 then
    natLenBits n.toNat + 1
  else
    let m : Int := -n - 1
    natLenBits m.toNat + 1

def popBitsTwos257 (n : Int) : VM BitString := do
  match intToBitsTwos n 257 with
  | .ok bs => pure bs
  | .error e => throw e

set_option maxHeartbeats 1000000 in
def execInstrArithContExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt op =>
      match op with
      | .pow2 =>
          let exp ← VM.popNatUpTo 1023
          VM.pushIntQuiet (.num (intPow2 exp)) false
      | .fitsx =>
          VM.checkUnderflow 2
          let bits ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => throw .intOv
          | .num n =>
              if intSignedFitsBits n bits then
                VM.push (.int x)
              else
                throw .intOv
      | .ufitsx =>
          VM.checkUnderflow 2
          let bits ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => throw .intOv
          | .num n =>
              if intUnsignedFitsBits n bits then
                VM.push (.int x)
              else
                throw .intOv
      | .qand =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b =>
              let ba ← popBitsTwos257 a
              let bb ← popBitsTwos257 b
              let bc := bitsAnd ba bb
              VM.pushIntQuiet (.num (bitsToIntSignedTwos bc)) true
      | .qor =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b =>
              let ba ← popBitsTwos257 a
              let bb ← popBitsTwos257 b
              let bc := bitsOr ba bb
              VM.pushIntQuiet (.num (bitsToIntSignedTwos bc)) true
      | .qxor =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b =>
              let ba ← popBitsTwos257 a
              let bb ← popBitsTwos257 b
              let bc := bitsXor ba bb
              VM.pushIntQuiet (.num (bitsToIntSignedTwos bc)) true
      | .qnot =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num n =>
              let bs ← popBitsTwos257 n
              let inv : BitString := bs.map (fun b => !b)
              VM.pushIntQuiet (.num (bitsToIntSignedTwos inv)) true
      | .qfitsx =>
          VM.checkUnderflow 2
          let bits ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => VM.push (.int .nan)
          | .num n =>
              let out : IntVal := if intSignedFitsBits n bits then x else .nan
              VM.pushIntQuiet out true
      | .qufitsx =>
          VM.checkUnderflow 2
          let bits ← VM.popNatUpTo 1023
          let x ← VM.popInt
          match x with
          | .nan => VM.push (.int .nan)
          | .num n =>
              let out : IntVal := if intUnsignedFitsBits n bits then x else .nan
              VM.pushIntQuiet out true
      | .qbitsize =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushSmallInt 0
          | .num n =>
              let width : Nat := signedBitsizeTvm n
              VM.pushSmallInt (Int.ofNat width)
      | .qmin =>
          let y ← VM.popInt
          let x ← VM.popInt
          VM.pushIntQuiet (x.min y) true
      | .isnan =>
          let x ← VM.popInt
          VM.pushSmallInt (if x.isValid then 0 else -1)
      | .chknan =>
          let x ← VM.popInt
          VM.pushIntQuiet x false
      | .qsgn =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num n =>
              if n < 0 then
                VM.pushSmallInt (-1)
              else if n = 0 then
                VM.pushSmallInt 0
              else
                VM.pushSmallInt 1
      | .qless =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a < b then -1 else 0)
      | .qequal =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a = b then -1 else 0)
      | .qleq =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a ≤ b then -1 else 0)
      | .qgreater =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a > b then -1 else 0)
      | .qneq =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a ≠ b then -1 else 0)
      | .qgeq =>
          let y ← VM.popInt
          let x ← VM.popInt
          match x, y with
          | .nan, _ => VM.pushIntQuiet .nan true
          | _, .nan => VM.pushIntQuiet .nan true
          | .num a, .num b => VM.pushSmallInt (if a ≥ b then -1 else 0)
      | _ =>
          next
  | _ =>
      next

end TvmLean
