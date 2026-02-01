import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArith (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .inc =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.inc) false
  | .dec =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.dec) false
  | .negate =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n => VM.pushIntQuiet (.num (-n)) false
  | .qnegate =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan true
      | .num n => VM.pushIntQuiet (.num (-n)) true
  | .add =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.add y) false
  | .addInt n =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a => VM.pushIntQuiet (.num (a + n)) false
  | .sub =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.sub y) false
  | .subr =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (y.sub x) false
  | .mulInt n =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a => VM.pushIntQuiet (.num (a * n)) false
  | .mul =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.mul y) false
  | .min =>
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b => VM.pushIntQuiet (.num (if a ≤ b then a else b)) false
      | _, _ => VM.pushIntQuiet .nan false
  | .max =>
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b => VM.pushIntQuiet (.num (if a ≤ b then b else a)) false
      | _, _ => VM.pushIntQuiet .nan false
  | .minmax =>
      let x ← VM.popInt
      let y ← VM.popInt
      match x, y with
      | .num a, .num b =>
          if a ≤ b then
            VM.pushIntQuiet (.num a) false
            VM.pushIntQuiet (.num b) false
          else
            VM.pushIntQuiet (.num b) false
            VM.pushIntQuiet (.num a) false
      | _, _ =>
          VM.pushIntQuiet .nan false
          VM.pushIntQuiet .nan false
  | .abs quiet =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n =>
          if n < 0 then
            VM.pushIntQuiet (.num (-n)) quiet
          else
            VM.pushIntQuiet (.num n) quiet
  | .mulShrModConst d roundMode z =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .num a, .num b =>
          let tmp : Int := a * b
          match d with
          | 1 =>
              let q := rshiftPow2Round tmp z roundMode
              VM.pushIntQuiet (.num q) false
          | 2 =>
              let r := modPow2Round tmp z roundMode
              VM.pushIntQuiet (.num r) false
          | 3 =>
              let q := rshiftPow2Round tmp z roundMode
              let r := modPow2Round tmp z roundMode
              VM.pushIntQuiet (.num q) false
              VM.pushIntQuiet (.num r) false
          | _ =>
              throw .invOpcode
      | _, _ =>
          -- NaN propagation for MVP.
          if d == 3 then
            VM.pushIntQuiet .nan false
            VM.pushIntQuiet .nan false
          else
            VM.pushIntQuiet .nan false
  | .divMod d roundMode addMode quiet =>
      let y ← VM.popInt
      let w ←
        if addMode then
          VM.popInt
        else
          pure (.num 0)
      let x ← VM.popInt
      match x, w, y with
      | .num xn, .num wn, .num yn =>
          if yn = 0 then
            if d == 3 then
              VM.pushIntQuiet .nan quiet
              VM.pushIntQuiet .nan quiet
            else
              VM.pushIntQuiet .nan quiet
          else if roundMode != -1 && roundMode != 0 && roundMode != 1 then
            throw .invOpcode
          else
            let t : Int := xn + wn
            let (q, r) := divModRound t yn roundMode
            match d with
            | 1 =>
                VM.pushIntQuiet (.num q) quiet
            | 2 =>
                VM.pushIntQuiet (.num r) quiet
            | 3 =>
                VM.pushIntQuiet (.num q) quiet
                VM.pushIntQuiet (.num r) quiet
            | _ =>
                throw .invOpcode
      | _, _, _ =>
          if d == 3 then
            VM.pushIntQuiet .nan quiet
            VM.pushIntQuiet .nan quiet
          else
            VM.pushIntQuiet .nan quiet
  | .mulDivMod d roundMode addMode quiet =>
      -- Matches C++ `exec_muldivmod` (arithops.cpp).
      let z ← VM.popInt
      let w ←
        if addMode then
          VM.popInt
        else
          pure (.num 0)
      let y ← VM.popInt
      let x ← VM.popInt
      match x, w, y, z with
      | .num xn, .num wn, .num yn, .num zn =>
          if zn = 0 then
            if d == 3 then
              VM.pushIntQuiet .nan quiet
              VM.pushIntQuiet .nan quiet
            else
              VM.pushIntQuiet .nan quiet
          else if roundMode != -1 && roundMode != 0 && roundMode != 1 then
            throw .invOpcode
          else
            let tmp : Int := xn * yn + wn
            let (q, r) := divModRound tmp zn roundMode
            match d with
            | 1 =>
                VM.pushIntQuiet (.num q) quiet
            | 2 =>
                VM.pushIntQuiet (.num r) quiet
            | 3 =>
                VM.pushIntQuiet (.num q) quiet
                VM.pushIntQuiet (.num r) quiet
            | _ =>
                throw .invOpcode
      | _, _, _, _ =>
          if d == 3 then
            VM.pushIntQuiet .nan quiet
            VM.pushIntQuiet .nan quiet
          else
            VM.pushIntQuiet .nan quiet
  | .lshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n => VM.pushIntQuiet (.num (n * intPow2 bits)) quiet
  | .rshiftConst quiet bits =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan quiet
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n bits)) quiet
  | .lshift =>
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n => VM.pushIntQuiet (.num (n * intPow2 shift)) false
  | .rshift =>
      let shift ← VM.popNatUpTo 1023
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) false
  | .equal =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.equalResult y) false
  | .neq =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a ≠ b then -1 else 0)
  | .and_ =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          let ba ←
            match intToBitsTwos a 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bb ←
            match intToBitsTwos b 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bc := bitsAnd ba bb
          let c := bitsToIntSignedTwos bc
          VM.pushIntQuiet (.num c) false
  | .or =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          let ba ←
            match intToBitsTwos a 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bb ←
            match intToBitsTwos b 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bc := bitsOr ba bb
          let c := bitsToIntSignedTwos bc
          VM.pushIntQuiet (.num c) false
  | .xor =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          let ba ←
            match intToBitsTwos a 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bb ←
            match intToBitsTwos b 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bc := bitsXor ba bb
          let c := bitsToIntSignedTwos bc
          VM.pushIntQuiet (.num c) false
  | .not_ =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n =>
          let bs ←
            match intToBitsTwos n 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let inv : BitString := bs.map (fun b => !b)
          VM.pushIntQuiet (.num (bitsToIntSignedTwos inv)) false
  | .sgn =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n =>
          if n < 0 then
            VM.pushSmallInt (-1)
          else if n = 0 then
            VM.pushSmallInt 0
          else
            VM.pushSmallInt 1
  | .less =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a < b then -1 else 0)
  | .leq =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a ≤ b then -1 else 0)
  | .greater =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a > b then -1 else 0)
  | .geq =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          VM.pushSmallInt (if a ≥ b then -1 else 0)
  | .cmp =>
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          if a < b then
            VM.pushSmallInt (-1)
          else if a = b then
            VM.pushSmallInt 0
          else
            VM.pushSmallInt 1
  | .lessInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a < y then -1 else 0)
  | .eqInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a = y then -1 else 0)
  | .gtInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a > y then -1 else 0)
  | .neqInt y =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num a =>
          VM.pushSmallInt (if a ≠ y then -1 else 0)
  | .pushNull =>
      VM.push .null
  | .isNull =>
      let v ← VM.pop
      match v with
      | .null => VM.pushSmallInt (-1)
      | _ => VM.pushSmallInt 0
  | .nullSwapIf =>
      VM.execNullSwapIf true 0 1
  | .nullSwapIfNot =>
      VM.execNullSwapIf false 0 1
  | .nullRotrIf =>
      VM.execNullSwapIf true 1 1
  | .nullRotrIfNot =>
      VM.execNullSwapIf false 1 1
  | .nullSwapIf2 =>
      VM.execNullSwapIf true 0 2
  | .nullSwapIfNot2 =>
      VM.execNullSwapIf false 0 2
  | .nullRotrIf2 =>
      VM.execNullSwapIf true 1 2
  | .nullRotrIfNot2 =>
      VM.execNullSwapIf false 1 2
  | _ => next

end TvmLean
