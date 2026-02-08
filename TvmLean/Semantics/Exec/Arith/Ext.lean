import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def popLongLike : VM Int := do
  let x ← VM.popInt
  match x with
  | .nan => pure (-1)
  | .num n => pure n

private def shiftOutOfRange (shift : Int) (max : Nat) : Bool :=
  decide (shift < 0 ∨ shift > Int.ofNat max)

private def bigintWordShift : Nat := 52
private def bigintWordBits : Nat := 64
private def bigintBase : Int := intPow2 bigintWordShift
private def bigintHalf : Int := intPow2 (bigintWordShift - 1)

private def intToBigInt52Digits (n : Int) : Array Int :=
  if n == 0 then
    #[0]
  else
    Id.run do
      let mut q : Int := n
      let mut out : Array Int := #[]
      while q != 0 do
        let r : Int := Int.emod q bigintBase
        let d : Int :=
          if decide (r >= bigintHalf) then
            r - bigintBase
          else
            r
        out := out.push d
        q := (q - d) / bigintBase
      if out.isEmpty then #[0] else out

private def addAnyNoNormalize (x y : Array Int) : Array Int :=
  if y.size <= x.size then
    Id.run do
      let mut out := x
      for i in [0:y.size] do
        out := out.set! i (out[i]! + y[i]!)
      out
  else
    Id.run do
      let mut out := y
      for i in [0:x.size] do
        out := out.set! i (out[i]! + x[i]!)
      out

private def rshiftPow2RoundAddCompat (x w : Int) (shift : Nat) (roundMode : Int) : Int :=
  -- C++ `exec_shrmod` (ADD* variants) applies `rshift` to a non-normalized
  -- temporary (`tmp += w` without normalize). For very large shifts, `rshift_any`
  -- uses fast-path sign checks on the non-normalized top word, which can differ
  -- from mathematically rounded `(x + w) / 2^shift`. Mirror that behavior here.
  let tmp : Int := x + w
  let xDigits := intToBigInt52Digits x
  let wDigits := intToBigInt52Digits w
  let tmpDigits := addAnyNoNormalize xDigits wDigits
  let fastLimit : Nat := tmpDigits.size * bigintWordShift + (bigintWordBits - bigintWordShift)
  if shift > fastLimit then
    let top : Int := tmpDigits[tmpDigits.size - 1]!
    if roundMode == 0 then
      0
    else if decide (roundMode < 0) then
      if decide (top < 0) then -1 else 0
    else
      if decide (top > 0) then 1 else 0
  else
    rshiftPow2Round tmp shift roundMode

private def rshiftPow2RoundInvalidCompat (shift : Nat) (roundMode : Int) : IntVal :=
  if shift == 0 then
    .nan
  else
    let fastLimit : Nat := bigintWordBits - bigintWordShift
    if decide (roundMode < 0) && shift > fastLimit then
      .num (-1)
    else
      .num 0

set_option maxHeartbeats 1000000 in
def execInstrArithExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .arithExt op =>
      match op with
      | .qaddInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a + n)) true
      | .qmulInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushIntQuiet (.num (a * n)) true
      | .qeqInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushSmallInt (if a = n then -1 else 0)
      | .qgtInt n =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan true
          | .num a => VM.pushSmallInt (if a > n then -1 else 0)
      | .fitsConst unsigned quiet bits =>
          let x ← VM.popInt
          match x with
          | .nan => VM.pushIntQuiet .nan quiet
          | .num n =>
              let ok :=
                if unsigned then
                  intUnsignedFitsBits n bits
                else
                  intSignedFitsBits n bits
              if ok then
                VM.push (.int x)
              else if quiet then
                VM.push (.int .nan)
              else
                throw .intOv
      | .lshiftVar quiet =>
          let shiftRaw ← popLongLike
          let badShift := shiftOutOfRange shiftRaw 1023
          if (!quiet) && badShift then
            throw .rangeChk
          let x ← VM.popInt
          if badShift then
            VM.pushIntQuiet .nan quiet
          else
            let shift : Nat := shiftRaw.toNat
            match x with
            | .nan => VM.pushIntQuiet .nan quiet
            | .num n => VM.pushIntQuiet (.num (n * intPow2 shift)) quiet
      | .rshiftVar quiet =>
          let shiftRaw ← popLongLike
          let badShift := shiftOutOfRange shiftRaw 1023
          if (!quiet) && badShift then
            throw .rangeChk
          let x ← VM.popInt
          if badShift then
            VM.pushIntQuiet .nan quiet
          else
            let shift : Nat := shiftRaw.toNat
            match x with
            | .nan => VM.pushIntQuiet .nan quiet
            | .num n => VM.pushIntQuiet (.num (floorDivPow2 n shift)) quiet
      | .shrMod mulMode addMode d roundMode quiet zOpt =>
          if mulMode then
            -- MULRSHIFT/MULMODPOW2 family: runtime shift range checks are relaxed in quiet mode
            -- (global version >= 13), producing NaN instead of throwing.
            -- Like C++ `exec_mulshrmod`, enforce stack depth before popping shift:
            -- runtime-shift variants need 3 args (`x y z`) or 4 with add-mode.
            -- const-shift variants need 2 args (`x y`) or 3 with add-mode.
            let st ← get
            let need : Nat :=
              if zOpt.isSome then
                if addMode then 3 else 2
              else
                if addMode then 4 else 3
            if st.stack.size < need then
              throw .stkUnd
            let shiftRaw ←
              match zOpt with
              | some z => pure (Int.ofNat z)
              | none => popLongLike
            let badShift := shiftOutOfRange shiftRaw 256
            if (!quiet) && badShift then
              throw .rangeChk
            let w ← if addMode then VM.popInt else pure (.num 0)
            let y ← VM.popInt
            let x ← VM.popInt
            if badShift then
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
            else
              match x, y, w with
              | .num xn, .num yn, .num wn =>
                  let shift : Nat := shiftRaw.toNat
                  let roundMode' : Int :=
                    if zOpt.isNone && shift == 0 then
                      -1
                    else
                      roundMode
                  if roundMode' != -1 && roundMode' != 0 && roundMode' != 1 then
                    throw .invOpcode
                  let tmp0 : Int := xn * yn
                  let tmp : Int := if addMode then tmp0 + wn else tmp0
                  match d with
                  | 1 =>
                      let q := rshiftPow2Round tmp shift roundMode'
                      VM.pushIntQuiet (.num q) quiet
                  | 2 =>
                      let r := modPow2Round tmp shift roundMode'
                      VM.pushIntQuiet (.num r) quiet
                  | 3 =>
                      let q := rshiftPow2Round tmp shift roundMode'
                      let r := modPow2Round tmp shift roundMode'
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
          else
            -- RSHIFT/MODPOW2 family: runtime shift is strict `pop_smallint_range(256)` even in quiet mode.
            let st ← get
            let need : Nat :=
              if zOpt.isSome then
                if addMode then 2 else 1
              else
                if addMode then 3 else 2
            if st.stack.size < need then
              throw .stkUnd
            let shift : Nat ←
              match zOpt with
              | some z => pure z
              | none => VM.popNatUpTo 256
            let w ← if addMode then VM.popInt else pure (.num 0)
            let x ← VM.popInt
            let roundMode' : Int :=
              if zOpt.isNone && shift == 0 then
                -1
              else
                roundMode
            if roundMode' != -1 && roundMode' != 0 && roundMode' != 1 then
              throw .invOpcode
            match x, w with
            | .num xn, .num wn =>
                let tmp : Int := if addMode then xn + wn else xn
                let qCompat : Int :=
                  if addMode then
                    rshiftPow2RoundAddCompat xn wn shift roundMode'
                  else
                    rshiftPow2Round tmp shift roundMode'
                match d with
                | 1 =>
                    VM.pushIntQuiet (.num qCompat) quiet
                | 2 =>
                    let r := modPow2Round tmp shift roundMode'
                    VM.pushIntQuiet (.num r) quiet
                | 3 =>
                    let r := modPow2Round tmp shift roundMode'
                    VM.pushIntQuiet (.num qCompat) quiet
                    VM.pushIntQuiet (.num r) quiet
                | _ =>
                    throw .invOpcode
            | .nan, .num _ =>
                if !addMode && d == 1 then
                  VM.pushIntQuiet (rshiftPow2RoundInvalidCompat shift roundMode') quiet
                else if d == 3 then
                  VM.pushIntQuiet .nan quiet
                  VM.pushIntQuiet .nan quiet
                else
                  VM.pushIntQuiet .nan quiet
            | _, _ =>
                if d == 3 then
                  VM.pushIntQuiet .nan quiet
                  VM.pushIntQuiet .nan quiet
                else
                  VM.pushIntQuiet .nan quiet
      | .shlDivMod d roundMode addMode quiet zOpt =>
          -- TVM `exec_shldivmod` checks arity first, then pops runtime shift
          -- (when present), then divisor.
          let st ← get
          let need : Nat :=
            if zOpt.isSome then
              if addMode then 3 else 2
            else
              if addMode then 4 else 3
          if st.stack.size < need then
            throw .stkUnd
          let shiftRaw ←
            match zOpt with
            | some z => pure (Int.ofNat z)
            | none => popLongLike
          let badShift := shiftOutOfRange shiftRaw 256
          if (!quiet) && badShift then
            throw .rangeChk
          let y ← VM.popInt
          let w ← if addMode then VM.popInt else pure (.num 0)
          let x ← VM.popInt
          if badShift then
              if d == 3 then
                VM.pushIntQuiet .nan quiet
                VM.pushIntQuiet .nan quiet
              else
                VM.pushIntQuiet .nan quiet
          else
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
                  let shift : Nat := shiftRaw.toNat
                  let tmp : Int := xn * intPow2 shift + wn
                  let (q, r) := divModRound tmp yn roundMode
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
  | _ => next

end TvmLean
