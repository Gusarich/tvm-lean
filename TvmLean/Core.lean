import Std

namespace TvmLean

/-! A small, executable “Milestone 1” core:

- Core datatypes (`IntVal`, `Value`, `Continuation`, `VmState`)
- A tiny instruction AST and an executable `step`
- Minimal cp0 decode/encode utilities (Milestone 2)
- WF predicates + theorem statements (mostly `sorry` for now)

This is intentionally minimal and designed to be refactored as we add decoding/cells/dicts/opcodes.
-/

inductive Excno : Type
  | none
  | alt
  | stkUnd
  | stkOv
  | intOv
  | rangeChk
  | invOpcode
  | typeChk
  | cellOv
  | cellUnd
  | dictErr
  | unknown
  | fatal
  | outOfGas
  | virtErr
  deriving DecidableEq, Repr

def Excno.toInt : Excno → Int
  | .none => 0
  | .alt => 1
  | .stkUnd => 2
  | .stkOv => 3
  | .intOv => 4
  | .rangeChk => 5
  | .invOpcode => 6
  | .typeChk => 7
  | .cellOv => 8
  | .cellUnd => 9
  | .dictErr => 10
  | .unknown => 11
  | .fatal => 12
  | .outOfGas => 13
  | .virtErr => 14

instance : ToString Excno := ⟨fun
  | .none => "none"
  | .alt => "alt"
  | .stkUnd => "stkUnd"
  | .stkOv => "stkOv"
  | .intOv => "intOv"
  | .rangeChk => "rangeChk"
  | .invOpcode => "invOpcode"
  | .typeChk => "typeChk"
  | .cellOv => "cellOv"
  | .cellUnd => "cellUnd"
  | .dictErr => "dictErr"
  | .unknown => "unknown"
  | .fatal => "fatal"
  | .outOfGas => "outOfGas"
  | .virtErr => "virtErr"⟩

@[extern "tvmlean_ed25519_verify"]
opaque ed25519Verify (msg pk sig : ByteArray) : Bool

inductive IntVal : Type
  | nan
  | num (n : Int)
  deriving DecidableEq, Repr

def IntVal.isValid : IntVal → Bool
  | .nan => false
  | .num _ => true

def IntVal.signedFits257 : IntVal → Bool
  | .nan => false
  | .num n =>
      -- [-2^256, 2^256)
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      decide (lo ≤ n ∧ n < hi)

def IntVal.add (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a + b)
  | _, _ => .nan

def IntVal.sub (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a - b)
  | _, _ => .nan

def IntVal.mul (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a * b)
  | _, _ => .nan

def IntVal.inc (x : IntVal) : IntVal :=
  x.add (.num 1)

def IntVal.dec (x : IntVal) : IntVal :=
  x.sub (.num 1)

def IntVal.equalResult (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => if a = b then .num (-1) else .num 0
  | _, _ => .nan

def IntVal.toBool? (x : IntVal) : Except Excno Bool :=
  match x with
  | .nan => .error .intOv
  | .num n => .ok (n ≠ 0)

abbrev BitString := Array Bool

def bitsToNat (bs : BitString) : Nat :=
  bs.foldl (fun acc b => (acc <<< 1) + (if b then 1 else 0)) 0

def bitsStripTrailingMarker (bs : BitString) : BitString :=
  -- Mirrors `CellSlice::remove_trailing()` from C++: remove trailing zeros and then one more bit (the marker).
  Id.run do
    if bs.size == 0 then
      return bs
    let mut trailing : Nat := 0
    while trailing < bs.size && bs[bs.size - 1 - trailing]! = false do
      trailing := trailing + 1
    if trailing == bs.size then
      return #[]
    return bs.take (bs.size - (trailing + 1))

def natToBits (n bits : Nat) : BitString :=
  Array.ofFn (n := bits) fun i =>
    let k := bits - 1 - i.1
    n.testBit k

def intPow2 (bits : Nat) : Int :=
  (2 : Int) ^ bits

def intSignedFitsBits (n : Int) (bits : Nat) : Bool :=
  if bits == 0 then
    n == 0
  else
    let half : Int := intPow2 (bits - 1)
    decide (-half ≤ n ∧ n < half)

def floorDivPow2 (n : Int) (bits : Nat) : Int :=
  if bits == 0 then
    n
  else
    let p : Int := intPow2 bits
    if decide (n ≥ 0) then
      n / p
    else
      -- floor(-a / p) = -ceil(a / p)
      let a : Int := -n
      let q : Int := (a + p - 1) / p
      (-q)

def ceilDivPow2 (n : Int) (bits : Nat) : Int :=
  if bits == 0 then
    n
  else
    let p : Int := intPow2 bits
    if decide (n ≥ 0) then
      (n + p - 1) / p
    else
      -- ceil(-a / p) = -floor(a / p)
      let a : Int := -n
      (- (a / p))

def roundNearestDivPow2 (n : Int) (bits : Nat) : Int :=
  -- Round to nearest, ties away from zero (matches BigInt `round_mode = 0` behavior for pow2 shifts).
  if bits == 0 then
    n
  else
    let half : Int := intPow2 (bits - 1)
    let p : Int := intPow2 bits
    if decide (n ≥ 0) then
      (n + half) / p
    else
      -(((-n) + half) / p)

def rshiftPow2Round (n : Int) (bits : Nat) (roundMode : Int) : Int :=
  if decide (roundMode < 0) then
    floorDivPow2 n bits
  else if roundMode == 0 then
    roundNearestDivPow2 n bits
  else
    ceilDivPow2 n bits

def euclidModPow2 (n : Int) (bits : Nat) : Int :=
  -- Euclidean remainder in [0, 2^bits), even for negative `n`.
  if bits == 0 then
    0
  else
    let p : Int := intPow2 bits
    if decide (n ≥ 0) then
      n % p
    else
      let m := (-n) % p
      if m == 0 then 0 else p - m

def modPow2Round (n : Int) (bits : Nat) (roundMode : Int) : Int :=
  if bits == 0 then
    0
  else if decide (roundMode < 0) then
    euclidModPow2 n bits
  else if decide (roundMode > 0) then
    -euclidModPow2 (-n) bits
  else
    if intSignedFitsBits n bits then
      n
    else
      let p : Int := intPow2 bits
      let r0 := euclidModPow2 n bits
      let half : Int := intPow2 (bits - 1)
      if decide (r0 ≥ half) then
        r0 - p
      else
        r0

def intAbs (n : Int) : Int :=
  if decide (n < 0) then -n else n

def floorDiv (x y : Int) : Int :=
  -- Floor division (towards -∞), for non-zero `y`.
  if y = 0 then
    0
  else
    let q0 : Int := x / y
    let r0 : Int := x - q0 * y
    if r0 = 0 then
      q0
    else
      let sx : Bool := decide (x < 0)
      let sy : Bool := decide (y < 0)
      if sx != sy then
        q0 - 1
      else
        q0

def ceilDiv (x y : Int) : Int :=
  -- Ceil division (towards +∞), for non-zero `y`.
  -floorDiv (-x) y

def divModRound (x y : Int) (roundMode : Int) : (Int × Int) :=
  -- Division with TVM rounding modes:
  --   roundMode = -1: floor
  --   roundMode =  0: nearest, ties away from zero
  --   roundMode =  1: ceil
  if y = 0 then
    (0, 0)
  else if roundMode = -1 then
    let q := floorDiv x y
    (q, x - q * y)
  else if roundMode = 1 then
    let q := ceilDiv x y
    (q, x - q * y)
  else
    let qF := floorDiv x y
    let rF := x - qF * y
    let ay := intAbs y
    let ar := intAbs rF
    let twoAr := ar * 2
    let q :=
      if decide (twoAr < ay) then
        qF
      else if decide (twoAr > ay) then
        qF + 1
      else
        -- tie: away from zero
        if decide (x * y ≥ 0) then qF + 1 else qF
    (q, x - q * y)

/-! Minimal SHA256 (used for TON cell hashes).

This is engineering code for diff-testing and coverage; it is not formally verified yet.
We implement the standard SHA-256 compression over big-endian message words.
-/

def sha256K : Array UInt32 :=
  #[
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ].map UInt32.ofNat

def sha256Init : Array UInt32 :=
  #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ].map UInt32.ofNat

def u32rotr (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> (UInt32.ofNat n)) ||| (x <<< (UInt32.ofNat (32 - n)))

def shaCh (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

def shaMaj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def shaBigSigma0 (x : UInt32) : UInt32 :=
  u32rotr x 2 ^^^ u32rotr x 13 ^^^ u32rotr x 22

def shaBigSigma1 (x : UInt32) : UInt32 :=
  u32rotr x 6 ^^^ u32rotr x 11 ^^^ u32rotr x 25

def shaSmallSigma0 (x : UInt32) : UInt32 :=
  u32rotr x 7 ^^^ u32rotr x 18 ^^^ (x >>> 3)

def shaSmallSigma1 (x : UInt32) : UInt32 :=
  u32rotr x 17 ^^^ u32rotr x 19 ^^^ (x >>> 10)

def u32FromBytesBE (b0 b1 b2 b3 : UInt8) : UInt32 :=
  ((UInt32.ofNat b0.toNat) <<< 24) ||| ((UInt32.ofNat b1.toNat) <<< 16) ||| ((UInt32.ofNat b2.toNat) <<< 8) ||| (UInt32.ofNat b3.toNat)

def sha256Pad (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let bitLen : Nat := msg.size * 8
    let mut out := msg.push 0x80
    while out.size % 64 ≠ 56 do
      out := out.push 0
    for i in [0:8] do
      let shift := (7 - i) * 8
      out := out.push (UInt8.ofNat ((bitLen >>> shift) &&& 0xff))
    out

def sha256Digest (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let padded := sha256Pad msg
    let mut h := sha256Init
    let blocks := padded.size / 64
    for bi in [0:blocks] do
      let base := bi * 64
      let mut w : Array UInt32 := Array.mkArray 64 0
      for i in [0:16] do
        let j := base + i * 4
        let b0 := padded[j]!
        let b1 := padded[j + 1]!
        let b2 := padded[j + 2]!
        let b3 := padded[j + 3]!
        w := w.set! i (u32FromBytesBE b0 b1 b2 b3)
      for i in [16:64] do
        let s0 := shaSmallSigma0 (w[i - 15]!)
        let s1 := shaSmallSigma1 (w[i - 2]!)
        w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)

      let mut a := h[0]!
      let mut b := h[1]!
      let mut c := h[2]!
      let mut d := h[3]!
      let mut e := h[4]!
      let mut f := h[5]!
      let mut g := h[6]!
      let mut hh := h[7]!

      for i in [0:64] do
        let t1 := hh + shaBigSigma1 e + shaCh e f g + sha256K[i]! + w[i]!
        let t2 := shaBigSigma0 a + shaMaj a b c
        hh := g
        g := f
        f := e
        e := d + t1
        d := c
        c := b
        b := a
        a := t1 + t2

      h := h.set! 0 (h[0]! + a)
      h := h.set! 1 (h[1]! + b)
      h := h.set! 2 (h[2]! + c)
      h := h.set! 3 (h[3]! + d)
      h := h.set! 4 (h[4]! + e)
      h := h.set! 5 (h[5]! + f)
      h := h.set! 6 (h[6]! + g)
      h := h.set! 7 (h[7]! + hh)

    let mut out : Array UInt8 := #[]
    for i in [0:8] do
      let x := h[i]!
      out := out.push (UInt8.ofNat ((x >>> 24).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 16).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 8).toNat &&& 0xff))
      out := out.push (UInt8.ofNat (x.toNat &&& 0xff))
    out

/-! Minimal SHA512 (used for TON PRNG: RANDU256 / RAND).

This is engineering code for diff-testing and coverage; it is not formally verified yet.
-/

def sha512K : Array UInt64 :=
  #[
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
  ].map UInt64.ofNat

def sha512Init : Array UInt64 :=
  #[
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
  ].map UInt64.ofNat

def u64rotr (x : UInt64) (n : Nat) : UInt64 :=
  (x >>> (UInt64.ofNat n)) ||| (x <<< (UInt64.ofNat (64 - n)))

def sha512Ch (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

def sha512Maj (x y z : UInt64) : UInt64 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def sha512BigSigma0 (x : UInt64) : UInt64 :=
  u64rotr x 28 ^^^ u64rotr x 34 ^^^ u64rotr x 39

def sha512BigSigma1 (x : UInt64) : UInt64 :=
  u64rotr x 14 ^^^ u64rotr x 18 ^^^ u64rotr x 41

def sha512SmallSigma0 (x : UInt64) : UInt64 :=
  u64rotr x 1 ^^^ u64rotr x 8 ^^^ (x >>> 7)

def sha512SmallSigma1 (x : UInt64) : UInt64 :=
  u64rotr x 19 ^^^ u64rotr x 61 ^^^ (x >>> 6)

def u64FromBytesBE (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  ((UInt64.ofNat b0.toNat) <<< 56) ||| ((UInt64.ofNat b1.toNat) <<< 48) ||| ((UInt64.ofNat b2.toNat) <<< 40) |||
    ((UInt64.ofNat b3.toNat) <<< 32) ||| ((UInt64.ofNat b4.toNat) <<< 24) ||| ((UInt64.ofNat b5.toNat) <<< 16) |||
    ((UInt64.ofNat b6.toNat) <<< 8) ||| (UInt64.ofNat b7.toNat)

def sha512Pad (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let bitLen : Nat := msg.size * 8
    let mut out := msg.push 0x80
    while out.size % 128 ≠ 112 do
      out := out.push 0
    for i in [0:16] do
      let shift := (15 - i) * 8
      out := out.push (UInt8.ofNat ((bitLen >>> shift) &&& 0xff))
    out

def sha512Digest (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let padded := sha512Pad msg
    let mut h := sha512Init
    let blocks := padded.size / 128
    for bi in [0:blocks] do
      let base := bi * 128
      let mut w : Array UInt64 := Array.replicate 80 0
      for i in [0:16] do
        let j := base + i * 8
        let b0 := padded[j]!
        let b1 := padded[j + 1]!
        let b2 := padded[j + 2]!
        let b3 := padded[j + 3]!
        let b4 := padded[j + 4]!
        let b5 := padded[j + 5]!
        let b6 := padded[j + 6]!
        let b7 := padded[j + 7]!
        w := w.set! i (u64FromBytesBE b0 b1 b2 b3 b4 b5 b6 b7)
      for i in [16:80] do
        let s0 := sha512SmallSigma0 (w[i - 15]!)
        let s1 := sha512SmallSigma1 (w[i - 2]!)
        w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)

      let mut a := h[0]!
      let mut b := h[1]!
      let mut c := h[2]!
      let mut d := h[3]!
      let mut e := h[4]!
      let mut f := h[5]!
      let mut g := h[6]!
      let mut hh := h[7]!

      for i in [0:80] do
        let t1 := hh + sha512BigSigma1 e + sha512Ch e f g + sha512K[i]! + w[i]!
        let t2 := sha512BigSigma0 a + sha512Maj a b c
        hh := g
        g := f
        f := e
        e := d + t1
        d := c
        c := b
        b := a
        a := t1 + t2

      h := h.set! 0 (h[0]! + a)
      h := h.set! 1 (h[1]! + b)
      h := h.set! 2 (h[2]! + c)
      h := h.set! 3 (h[3]! + d)
      h := h.set! 4 (h[4]! + e)
      h := h.set! 5 (h[5]! + f)
      h := h.set! 6 (h[6]! + g)
      h := h.set! 7 (h[7]! + hh)

    let mut out : Array UInt8 := #[]
    for i in [0:8] do
      let x := h[i]!
      out := out.push (UInt8.ofNat ((x >>> 56).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 48).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 40).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 32).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 24).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 16).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 8).toNat &&& 0xff))
      out := out.push (UInt8.ofNat (x.toNat &&& 0xff))
    out

structure Cell where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Cell.empty : Cell :=
  { bits := #[], refs := #[] }

instance : Inhabited Cell := ⟨Cell.empty⟩

partial def Cell.beq (a b : Cell) : Bool :=
  a.bits == b.bits &&
    a.refs.size == b.refs.size &&
      Id.run do
        let mut ok := true
        for i in [0:a.refs.size] do
          if !(Cell.beq a.refs[i]! b.refs[i]!) then
            ok := false
        return ok

instance : BEq Cell := ⟨Cell.beq⟩

def Cell.ofUInt (bits : Nat) (n : Nat) : Cell :=
  { bits := natToBits n bits, refs := #[] }

def Cell.depthLe (c : Cell) : Nat → Bool
  | 0 => false
  | limit + 1 =>
      c.refs.all (fun r => r.depthLe limit)

def bitsToByte (bs : BitString) (start len : Nat) : UInt8 :=
  Id.run do
    let mut acc : Nat := 0
    for j in [0:len] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    UInt8.ofNat acc

def bitsToPaddedLastByte (bs : BitString) (start usedBits : Nat) : UInt8 :=
  -- `usedBits` ∈ {1..7}: data bits in the high bits, then a single `1` tag bit, then zeros.
  Id.run do
    let mut acc : Nat := 0
    for j in [0:usedBits] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    acc := acc ||| (1 <<< (7 - usedBits))
    UInt8.ofNat acc

def bytesToNatBE (bs : Array UInt8) : Nat :=
  bs.foldl (fun acc b => (acc <<< 8) + b.toNat) 0

def natToBytesBEFixed (n : Nat) (len : Nat) : Array UInt8 :=
  Array.ofFn (n := len) fun i =>
    let shift := (len - 1 - i.1) * 8
    UInt8.ofNat ((n >>> shift) &&& 0xff)

def bitStringToBytesBE (bs : BitString) : Array UInt8 :=
  -- Mirrors `td::BitSliceWrite{buffer, bytes*8} = prefetch_bits(bytes*8)` used by `CellSlice::prefetch_bytes`.
  -- Bit order: first bit is the MSB of the first byte.
  Id.run do
    let bytes : Nat := bs.size / 8
    let mut out : Array UInt8 := #[]
    for i in [0:bytes] do
      out := out.push (bitsToByte bs (i * 8) 8)
    out

def uint256Limit : Nat := 1 <<< 256

def exportUInt256BE (x : IntVal) : Except Excno (Array UInt8) := do
  match x with
  | .nan => throw .rangeChk
  | .num n =>
      if n < 0 then
        throw .rangeChk
      let u : Nat := n.toNat
      if u ≥ uint256Limit then
        throw .rangeChk
      return natToBytesBEFixed u 32

partial def Cell.depth (c : Cell) : Nat :=
  if c.refs.isEmpty then
    0
  else
    1 + c.refs.foldl (fun m r => Nat.max m (Cell.depth r)) 0

partial def Cell.hashBytes (c : Cell) : Array UInt8 :=
  Id.run do
    let refsCnt : Nat := c.refs.size
    let bitLen : Nat := c.bits.size
    let fullBytes : Nat := bitLen / 8
    let remBits : Nat := bitLen % 8
    let d1 : Nat := refsCnt
    let d2 : Nat := (fullBytes <<< 1) + (if remBits ≠ 0 then 1 else 0)

    let mut msg : Array UInt8 := #[UInt8.ofNat d1, UInt8.ofNat d2]
    for i in [0:fullBytes] do
      msg := msg.push (bitsToByte c.bits (i * 8) 8)
    if remBits ≠ 0 then
      msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)

    -- Child depths (big-endian 16-bit).
    for i in [0:refsCnt] do
      let d := Cell.depth c.refs[i]!
      msg := msg.push (UInt8.ofNat ((d >>> 8) &&& 0xff))
      msg := msg.push (UInt8.ofNat (d &&& 0xff))

    -- Child hashes.
    for i in [0:refsCnt] do
      let h := Cell.hashBytes c.refs[i]!
      for b in h do
        msg := msg.push b

    sha256Digest msg

structure Slice where
  cell : Cell
  bitPos : Nat
  refPos : Nat
  deriving Repr

def Slice.ofCell (c : Cell) : Slice :=
  { cell := c, bitPos := 0, refPos := 0 }

def Slice.bitsRemaining (s : Slice) : Nat :=
  s.cell.bits.size - s.bitPos

def Slice.refsRemaining (s : Slice) : Nat :=
  s.cell.refs.size - s.refPos

def Slice.toCellRemaining (s : Slice) : Cell :=
  { bits := s.cell.bits.extract s.bitPos s.cell.bits.size
    refs := s.cell.refs.extract s.refPos s.cell.refs.size }

def Slice.haveBits (s : Slice) (n : Nat) : Bool :=
  decide (s.bitPos + n ≤ s.cell.bits.size)

def Slice.haveRefs (s : Slice) (n : Nat) : Bool :=
  decide (s.refPos + n ≤ s.cell.refs.size)

def Slice.readBits (s : Slice) (n : Nat) : BitString :=
  s.cell.bits.extract s.bitPos (s.bitPos + n)

def Slice.prefetchBytesCellUnd (s : Slice) (bytes : Nat) : Except Excno (Array UInt8) := do
  let bits : Nat := bytes * 8
  if s.haveBits bits then
    return bitStringToBytesBE (s.readBits bits)
  else
    throw .cellUnd

def Slice.advanceBits (s : Slice) (n : Nat) : Slice :=
  { s with bitPos := s.bitPos + n }

def Slice.takeRefCell (s : Slice) : Except Excno (Cell × Slice) := do
  if s.haveRefs 1 then
    let c := s.cell.refs[s.refPos]!
    let s' := { s with refPos := s.refPos + 1 }
    return (c, s')
  else
    throw .cellUnd

structure Builder where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Builder.empty : Builder :=
  { bits := #[], refs := #[] }

def Builder.canExtendBy (b : Builder) (bits : Nat) (refs : Nat := 0) : Bool :=
  decide (b.bits.size + bits ≤ 1023 ∧ b.refs.size + refs ≤ 4)

def Builder.storeBits (b : Builder) (bs : BitString) : Builder :=
  { b with bits := b.bits ++ bs }

def Builder.finalize (b : Builder) : Cell :=
  { bits := b.bits, refs := b.refs }

inductive DictSetMode : Type
  | set
  | replace
  | add
  deriving DecidableEq, Repr

inductive Instr : Type
  | nop
  | pushInt (n : IntVal)
  | pushPow2 (exp : Nat) -- PUSHPOW2 <exp>
  | pushPow2Dec (exp : Nat) -- PUSHPOW2DEC <exp>  (2^exp - 1)
  | pushNegPow2 (exp : Nat) -- PUSHNEGPOW2 <exp>  (-2^exp)
  | push (idx : Nat)    -- PUSH s[idx]
  | pop (idx : Nat)     -- POP s[idx]
  | xchg0 (idx : Nat)   -- XCHG s0,s[idx]
  | xchg1 (idx : Nat)   -- XCHG s1,s[idx]
  | xchg (x : Nat) (y : Nat) -- XCHG s<x>,s<y>
  | xchg2 (x : Nat) (y : Nat) -- XCHG2 s<x>,s<y>
  | xchg3 (x : Nat) (y : Nat) (z : Nat) -- XCHG3 s<x>,s<y>,s<z>
  | xcpu (x : Nat) (y : Nat) -- XCPU s<x>,s<y>
  | xc2pu (x : Nat) (y : Nat) (z : Nat) -- XC2PU s<x>,s<y>,s<z>
  | xcpuxc (x : Nat) (y : Nat) (z : Nat) -- XCPUXC s<x>,s<y>,s<z-1>
  | xcpu2 (x : Nat) (y : Nat) (z : Nat) -- XCPU2 s<x>,s<y>,s<z>
  | puxc2 (x : Nat) (y : Nat) (z : Nat) -- PUXC2 s<x>,s<y-1>,s<z-1>
  | puxc (x : Nat) (y : Nat) -- PUXC s<x>,s<y-1> (see C++ stackops)
  | puxcpu (x : Nat) (y : Nat) (z : Nat) -- PUXCPU s<x>,s<y-1>,s<z-1>
  | push2 (x : Nat) (y : Nat) -- PUSH2 s<x>,s<y>
  | push3 (x : Nat) (y : Nat) (z : Nat) -- PUSH3 s<x>,s<y>,s<z>
  | blkSwap (x : Nat) (y : Nat) -- BLKSWAP <x>,<y>
  | rot                -- ROT
  | rotRev             -- ROTREV
  | twoSwap            -- 2SWAP
  | twoOver            -- 2OVER
  | reverse (x : Nat) (y : Nat) -- REVERSE <x>,<y>
  | tuck               -- TUCK
  | pushCtr (idx : Nat) -- PUSHCTRX <idx> (we'll use it for c4/c5/c7 too)
  | popCtr (idx : Nat)  -- POPCTRX <idx>
  | setContCtr (idx : Nat) -- SETCONTCTR c<idx>
  | ctos
  | xctos
  | newc
  | endc
  | ends
  | ldu (bits : Nat)
  | loadInt (unsigned : Bool) (prefetch : Bool) (quiet : Bool) (bits : Nat)
  | loadIntVar (unsigned : Bool) (prefetch : Bool) (quiet : Bool) -- {P}LD{I,U}X{Q}
  | ldref
  | pldRefIdx (idx : Nat) -- PLDREFIDX <idx>
  | loadSliceX (prefetch : Bool) (quiet : Bool) -- {PLD,LD}SLICEX{Q}
  | loadSliceFixed (prefetch : Bool) (quiet : Bool) (bits : Nat) -- {P}LDSLICE{Q} <bits>
  | sti (bits : Nat)
  | stu (bits : Nat)
  | stIntVar (unsigned : Bool) (rev : Bool) (quiet : Bool) -- ST{I,U}X{R}{Q}
  | stIntFixed (unsigned : Bool) (rev : Bool) (quiet : Bool) (bits : Nat) -- ST{I,U}{R}{Q} <bits>
  | stSlice (rev : Bool) (quiet : Bool) -- {STSLICE,STSLICER}{Q?}
  | stSliceConst (s : Slice) -- STSLICECONST (inline constant slice)
  | stZeroes -- STZEROES
  | stOnes   -- STONES
  | stSame   -- STSAME
  | stref -- STREF
  | bbits -- BBITS
  | setcp (cp : Int)
  | ifret
  | ifnotret
  | if_         -- IF
  | ifnot       -- IFNOT
  | inc
  | dec
  | negate
  | add
  | addInt (n : Int) -- ADDINT <tinyint8>
  | sub
  | subr
  | mulInt (n : Int) -- MULINT <tinyint8>
  | mul
  | min
  | max
  | minmax
  | mulShrModConst (d : Nat) (roundMode : Int) (z : Nat) -- MUL{RSHIFT,MODPOW2,RSHIFTMOD}# <z>
  | divMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) -- {Q}{ADD}{DIV,MOD,DIVMOD}{R,C}
  | lshiftConst (quiet : Bool) (bits : Nat) -- {Q}LSHIFT <tinyint8+1>
  | rshiftConst (quiet : Bool) (bits : Nat) -- {Q}RSHIFT <tinyint8+1>
  | lshift            -- LSHIFT
  | rshift            -- RSHIFT
  | equal
  | neq
  | throw (exc : Int)      -- THROW <exc>
  | throwIf (exc : Int)    -- THROWIF <exc>
  | throwIfNot (exc : Int) -- THROWIFNOT <exc>
  | throwAny (hasParam : Bool) (hasCond : Bool) (throwCond : Bool) -- THROW{ARG}ANY{IF,IFNOT}
  | try_               -- TRY
  | saveCtr (idx : Nat)  -- SAVECTR c<idx> (currently stubbed)
  | sameAlt             -- SAMEALT
  | sameAltSave         -- SAMEALTSAVE (stubbed save)
  | boolAnd             -- BOOLAND
  | boolOr              -- BOOLOR
  | composBoth          -- COMPOSBOTH
  | setContVarArgs      -- SETCONTVARARGS
  | dictPushConst (dict : Cell) (keyBits : Nat) -- DICTPUSHCONST: pushes dict-root cell + key size
  | dictGet (intKey : Bool) (unsigned : Bool) (byRef : Bool) -- DICT{I,U}GET{REF?} / DICTGET{REF?}
  | dictGetExec (unsigned : Bool) (doCall : Bool) (pushZ : Bool) -- DICT{I,U}GET{JMP,EXEC}{Z?}
  | dictSet (intKey : Bool) (unsigned : Bool) (byRef : Bool) (mode : DictSetMode) -- DICT{I,U}{SET,REPLACE,ADD}{REF?}
  | dictReplaceB (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?REPLACEB (builder value)
  | stdict              -- STDICT
  | skipdict            -- SKIPDICT
  | lddict (preload : Bool) (quiet : Bool) -- {P}LDDICT{Q}
  | and_
  | or
  | not_
  | sgn
  | less
  | leq
  | greater
  | geq
  | cmp
  | sbits
  | srefs
  | sbitrefs
  | sempty            -- SEMPTY
  | sdempty           -- SDEMPTY
  | srempty           -- SREMPTY
  | sdCntTrail0        -- SDCNTTRAIL0
  | sdEq              -- SDEQ
  | sdcutfirst        -- SDCUTFIRST
  | sdskipfirst       -- SDSKIPFIRST
  | sdcutlast         -- SDCUTLAST
  | sdskiplast        -- SDSKIPLAST
  | sdBeginsX (quiet : Bool)        -- SDBEGINSX{Q}
  | sdBeginsConst (quiet : Bool) (pref : Slice) -- SDBEGINS{Q} <const>
  | lessInt (n : Int) -- LESSINT <tinyint8>
  | eqInt (n : Int)   -- EQINT <tinyint8>
  | gtInt (n : Int)   -- GTINT <tinyint8>
  | neqInt (n : Int)  -- NEQINT <tinyint8>
  | pushNull          -- PUSHNULL
  | isNull            -- ISNULL
  | nullSwapIfNot     -- NULLSWAPIFNOT
  | mktuple (n : Nat) -- TUPLE <n>
  | index (idx : Nat) -- INDEX <idx>
  | untuple (n : Nat) -- UNTUPLE <n>
  | tpush             -- TPUSH
  | blkdrop2 (x : Nat) (y : Nat) -- BLKDROP2 <x>,<y>
  | pushSliceConst (s : Slice) -- PUSHSLICE (inline constant slice)
  | pushCont (code : Slice) -- PUSHCONT (inline continuation)
  | pushRefCont (code : Cell) -- PUSHREFCONT (ref-based continuation)
  | execute
  | jmpx
  | callxArgs (params : Nat) (retVals : Int) -- CALLXARGS <params>,<retVals> (retVals may be -1)
  | jmpxArgs (params : Nat) -- JMPXARGS <params>
  | ret
  | retAlt
  | retBool
  | retArgs (n : Nat) -- RETARGS <n>
  | ifjmp
  | ifnotjmp
  | ifelse
  | ifref (code : Slice)       -- IFREF (1 ref)
  | ifnotref (code : Slice)    -- IFNOTREF (1 ref)
  | ifjmpref (code : Slice)    -- IFJMPREF (1 ref)
  | ifnotjmpref (code : Slice) -- IFNOTJMPREF (1 ref)
  | ifrefElse (code : Slice)   -- IFREFELSE (1 ref)
  | ifelseRef (code : Slice)   -- IFELSEREF (1 ref)
  | ifrefElseRef (t : Slice) (f : Slice) -- IFREFELSEREF (2 refs)
  | callRef (code : Slice)     -- CALLREF (1 ref)
  | callDict (idx : Nat)       -- CALLDICT <idx>
  | until             -- UNTIL
  | while_             -- WHILE
  | blkdrop (n : Nat) -- BLKDROP <n>
  | drop2              -- 2DROP
  | balance            -- BALANCE
  | now                -- NOW (TON environment)
  | getParam (idx : Nat) -- GETPARAM <idx> (0..15; TON environment)
  | randu256           -- RANDU256
  | rand               -- RAND
  | setRand (mix : Bool) -- SETRAND / ADDRAND
  | getGlobVar         -- GETGLOBVAR (c7[n])
  | getGlob (idx : Nat) -- GETGLOB <idx> (5-bit immediate)
  | setGlobVar         -- SETGLOBVAR (set c7[n])
  | setGlob (idx : Nat) -- SETGLOB <idx> (5-bit immediate)
  | accept             -- ACCEPT
  | setGasLimit        -- SETGASLIMIT
  | gasConsumed        -- GASCONSUMED
  | commit             -- COMMIT
  | ldGrams            -- LDGRAMS
  | stGrams            -- STGRAMS
  | ldMsgAddr (quiet : Bool) -- LDMSGADDR{Q}
  | rewriteStdAddr (quiet : Bool) -- REWRITESTDADDR{Q}
  | hashCU             -- HASHCU
  | hashSU             -- HASHSU
  | chkSignU           -- CHKSIGNU
  | chkSignS           -- CHKSIGNS
  | sendMsg            -- SENDMSG (stubbed fees)
  | sendRawMsg         -- SENDRAWMSG
  | rawReserve         -- RAWRESERVE
  deriving Repr

def Instr.pretty : Instr → String
  | .nop => "NOP"
  | .pushInt .nan => "PUSHINT NaN"
  | .pushInt (.num n) => s!"PUSHINT {n}"
  | .pushPow2 exp => s!"PUSHPOW2 {exp}"
  | .pushPow2Dec exp => s!"PUSHPOW2DEC {exp}"
  | .pushNegPow2 exp => s!"PUSHNEGPOW2 {exp}"
  | .push idx => s!"PUSH {idx}"
  | .pop idx => s!"POP {idx}"
  | .xchg0 idx => s!"XCHG_0 {idx}"
  | .xchg1 idx => s!"XCHG_1 {idx}"
  | .xchg x y => s!"XCHG {x},{y}"
  | .xchg2 x y => s!"XCHG2 {x},{y}"
  | .xchg3 x y z => s!"XCHG3 {x},{y},{z}"
  | .xcpu x y => s!"XCPU {x},{y}"
  | .xc2pu x y z => s!"XC2PU {x},{y},{z}"
  | .xcpuxc x y z => s!"XCPUXC {x},{y},{Int.ofNat z - 1}"
  | .xcpu2 x y z => s!"XCPU2 {x},{y},{z}"
  | .puxc2 x y z => s!"PUXC2 {x},{Int.ofNat y - 1},{Int.ofNat z - 1}"
  | .puxc x y => s!"PUXC {x},{Int.ofNat y - 1}"
  | .puxcpu x y z => s!"PUXCPU {x},{Int.ofNat y - 1},{Int.ofNat z - 1}"
  | .push2 x y => s!"PUSH2 {x},{y}"
  | .push3 x y z => s!"PUSH3 {x},{y},{z}"
  | .blkSwap x y => s!"BLKSWAP {x},{y}"
  | .rot => "ROT"
  | .rotRev => "ROTREV"
  | .twoSwap => "2SWAP"
  | .twoOver => "2OVER"
  | .reverse x y => s!"REVERSE {x},{y}"
  | .tuck => "TUCK"
  | .pushCtr idx => s!"PUSHCTR {idx}"
  | .popCtr idx => s!"POPCTR {idx}"
  | .setContCtr idx => s!"SETCONTCTR c{idx}"
  | .ctos => "CTOS"
  | .xctos => "XCTOS"
  | .newc => "NEWC"
  | .endc => "ENDC"
  | .ends => "ENDS"
  | .ldu bits => s!"LDU {bits}"
  | .loadInt unsigned prefetch quiet bits =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "U" else "I"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}{q} {bits}"
  | .loadIntVar unsigned prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "UX" else "IX"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}{q}"
  | .ldref => "LDREF"
  | .pldRefIdx idx => s!"PLDREFIDX {idx}"
  | .loadSliceX prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let q := if quiet then "Q" else ""
      s!"{p}SLICEX{q}"
  | .loadSliceFixed prefetch quiet bits =>
      let p := if prefetch then "PLD" else "LD"
      let q := if quiet then "Q" else ""
      s!"{p}SLICE{q} {bits}"
  | .sti bits => s!"STI {bits}"
  | .stu bits => s!"STU {bits}"
  | .stIntVar unsigned rev quiet =>
      let iu := if unsigned then "STUX" else "STIX"
      let r := if rev then "R" else ""
      let q := if quiet then "Q" else ""
      s!"{iu}{r}{q}"
  | .stIntFixed unsigned rev quiet bits =>
      let iu := if unsigned then "STU" else "STI"
      let r := if rev then "R" else ""
      let q := if quiet then "Q" else ""
      s!"{iu}{r}{q} {bits}"
  | .stSlice rev quiet =>
      let base := if rev then "STSLICER" else "STSLICE"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stSliceConst s => s!"STSLICECONST(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .stZeroes => "STZEROES"
  | .stOnes => "STONES"
  | .stSame => "STSAME"
  | .stref => "STREF"
  | .bbits => "BBITS"
  | .setcp cp => s!"SETCP {cp}"
  | .ifret => "IFRET"
  | .ifnotret => "IFNOTRET"
  | .if_ => "IF"
  | .ifnot => "IFNOT"
  | .inc => "INC"
  | .dec => "DEC"
  | .negate => "NEGATE"
  | .add => "ADD"
  | .addInt n => s!"ADDINT {n}"
  | .sub => "SUB"
  | .subr => "SUBR"
  | .mulInt n => s!"MULINT {n}"
  | .mul => "MUL"
  | .min => "MIN"
  | .max => "MAX"
  | .minmax => "MINMAX"
  | .mulShrModConst d roundMode z =>
      let base :=
        match d with
        | 1 => "MULRSHIFT"
        | 2 => "MULMODPOW2"
        | 3 => "MULRSHIFTMOD"
        | _ => "MULSHR/MOD"
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "F"
        else if roundMode = 1 then
          "R"
        else
          ""
      s!"{base}{suf}# {z}"
  | .divMod d roundMode addMode quiet =>
      let name :=
        (if addMode then "ADD" else "") ++
        (if (d &&& 1) = 1 then "DIV" else "") ++
        (if (d &&& 2) = 2 then "MOD" else "")
      let name := if quiet then "Q" ++ name else name
      let suf :=
        if roundMode = -1 then
          ""
        else if roundMode = 0 then
          "R"
        else if roundMode = 1 then
          "C"
        else
          ""
      name ++ suf
  | .lshiftConst quiet bits =>
      let q := if quiet then "Q" else ""
      s!"{q}LSHIFT {bits}"
  | .rshiftConst quiet bits =>
      let q := if quiet then "Q" else ""
      s!"{q}RSHIFT {bits}"
  | .lshift => "LSHIFT"
  | .rshift => "RSHIFT"
  | .equal => "EQUAL"
  | .neq => "NEQ"
  | .saveCtr idx => s!"SAVECTR {idx}"
  | .sameAlt => "SAMEALT"
  | .sameAltSave => "SAMEALTSAVE"
  | .boolAnd => "BOOLAND"
  | .boolOr => "BOOLOR"
  | .composBoth => "COMPOSBOTH"
  | .setContVarArgs => "SETCONTVARARGS"
  | .dictGet intKey unsigned byRef =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let r := if byRef then "REF" else ""
      s!"DICT{iu}GET{r}"
  | .throw exc => s!"THROW {exc}"
  | .throwIf exc => s!"THROWIF {exc}"
  | .throwIfNot exc => s!"THROWIFNOT {exc}"
  | .throwAny hasParam hasCond throwCond =>
      let arg := if hasParam then "ARG" else ""
      let cond :=
        if hasCond then
          if throwCond then "IF" else "IFNOT"
        else
          ""
      s!"THROW{arg}ANY{cond}"
  | .try_ => "TRY"
  | .dictPushConst _ keyBits => s!"DICTPUSHCONST {keyBits}"
  | .dictGetExec unsigned doCall pushZ =>
      let iu := if unsigned then "U" else "I"
      let je := if doCall then "EXEC" else "JMP"
      let z := if pushZ then "Z" else ""
      s!"DICT{iu}GET{je}{z}"
  | .dictSet intKey unsigned byRef mode =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let name :=
        match mode with
        | .set => "SET"
        | .replace => "REPLACE"
        | .add => "ADD"
      let r := if byRef then "REF" else ""
      s!"DICT{iu}{name}{r}"
  | .dictReplaceB intKey unsigned =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      s!"DICT{iu}REPLACEB"
  | .stdict => "STDICT"
  | .skipdict => "SKIPDICT"
  | .lddict preload quiet =>
      let p := if preload then "P" else ""
      let q := if quiet then "Q" else ""
      s!"{p}LDDICT{q}"
  | .and_ => "AND"
  | .or => "OR"
  | .not_ => "NOT"
  | .sgn => "SGN"
  | .less => "LESS"
  | .leq => "LEQ"
  | .greater => "GREATER"
  | .geq => "GEQ"
  | .cmp => "CMP"
  | .sbits => "SBITS"
  | .srefs => "SREFS"
  | .sbitrefs => "SBITREFS"
  | .sempty => "SEMPTY"
  | .sdempty => "SDEMPTY"
  | .srempty => "SREMPTY"
  | .sdCntTrail0 => "SDCNTTRAIL0"
  | .sdEq => "SDEQ"
  | .sdcutfirst => "SDCUTFIRST"
  | .sdskipfirst => "SDSKIPFIRST"
  | .sdcutlast => "SDCUTLAST"
  | .sdskiplast => "SDSKIPLAST"
  | .sdBeginsX quiet =>
      let q := if quiet then "Q" else ""
      s!"SDBEGINSX{q}"
  | .sdBeginsConst quiet pref =>
      let q := if quiet then "Q" else ""
      s!"SDBEGINS{q}(bits={pref.bitsRemaining})"
  | .lessInt n => s!"LESSINT {n}"
  | .eqInt n => s!"EQINT {n}"
  | .gtInt n => s!"GTINT {n}"
  | .neqInt n => s!"NEQINT {n}"
  | .pushNull => "PUSHNULL"
  | .isNull => "ISNULL"
  | .nullSwapIfNot => "NULLSWAPIFNOT"
  | .mktuple n => s!"TUPLE {n}"
  | .index idx => s!"INDEX {idx}"
  | .untuple n => s!"UNTUPLE {n}"
  | .tpush => "TPUSH"
  | .blkdrop2 x y => s!"BLKDROP2 {x},{y}"
  | .pushSliceConst s => s!"PUSHSLICE(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .pushCont code => s!"PUSHCONT(bits={code.bitsRemaining},refs={code.refsRemaining})"
  | .pushRefCont c => s!"PUSHREFCONT(bits={c.bits.size},refs={c.refs.size})"
  | .execute => "EXECUTE"
  | .jmpx => "JMPX"
  | .callxArgs params retVals => s!"CALLXARGS {params},{retVals}"
  | .jmpxArgs params => s!"JMPXARGS {params}"
  | .ret => "RET"
  | .retAlt => "RETALT"
  | .retBool => "RETBOOL"
  | .retArgs n => s!"RETARGS {n}"
  | .ifjmp => "IFJMP"
  | .ifnotjmp => "IFNOTJMP"
  | .ifelse => "IFELSE"
  | .ifref _ => "IFREF"
  | .ifnotref _ => "IFNOTREF"
  | .ifjmpref _ => "IFJMPREF"
  | .ifnotjmpref _ => "IFNOTJMPREF"
  | .ifrefElse _ => "IFREFELSE"
  | .ifelseRef _ => "IFELSEREF"
  | .ifrefElseRef _ _ => "IFREFELSEREF"
  | .callRef _ => "CALLREF"
  | .callDict idx => s!"CALLDICT {idx}"
  | .until => "UNTIL"
  | .while_ => "WHILE"
  | .blkdrop n => s!"BLKDROP {n}"
  | .drop2 => "2DROP"
  | .balance => "BALANCE"
  | .now => "NOW"
  | .getParam idx => s!"GETPARAM {idx}"
  | .randu256 => "RANDU256"
  | .rand => "RAND"
  | .setRand mix => if mix then "ADDRAND" else "SETRAND"
  | .getGlobVar => "GETGLOBVAR"
  | .getGlob idx => s!"GETGLOB {idx}"
  | .setGlobVar => "SETGLOBVAR"
  | .setGlob idx => s!"SETGLOB {idx}"
  | .accept => "ACCEPT"
  | .setGasLimit => "SETGASLIMIT"
  | .gasConsumed => "GASCONSUMED"
  | .commit => "COMMIT"
  | .ldGrams => "LDGRAMS"
  | .stGrams => "STGRAMS"
  | .ldMsgAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"LDMSGADDR{q}"
  | .rewriteStdAddr quiet =>
      let q := if quiet then "Q" else ""
      s!"REWRITESTDADDR{q}"
  | .hashCU => "HASHCU"
  | .hashSU => "HASHSU"
  | .chkSignU => "CHKSIGNU"
  | .chkSignS => "CHKSIGNS"
  | .sendMsg => "SENDMSG"
  | .sendRawMsg => "SENDRAWMSG"
  | .rawReserve => "RAWRESERVE"

instance : ToString Instr := ⟨Instr.pretty⟩

instance : BEq Instr := ⟨fun a b => reprStr a == reprStr b⟩

/- The structural `BEq` below is nicer and faster at runtime, but it makes Lean's
elaboration hit the default heartbeat limit due to the size of `Instr`.
Re-enable once we refactor `Instr` into smaller parts. -/
/-
instance : BEq Instr := ⟨fun a b =>
  match a, b with
  | .nop, .nop => true
  | .pushInt x, .pushInt y => x == y
  | .pushPow2 x, .pushPow2 y => x == y
  | .pushPow2Dec x, .pushPow2Dec y => x == y
  | .pushNegPow2 x, .pushNegPow2 y => x == y
  | .push x, .push y => x == y
  | .pop x, .pop y => x == y
  | .xchg0 x, .xchg0 y => x == y
  | .xchg1 x, .xchg1 y => x == y
  | .xchg x1 y1, .xchg x2 y2 => x1 == x2 && y1 == y2
  | .xchg2 x1 y1, .xchg2 x2 y2 => x1 == x2 && y1 == y2
  | .xchg3 x1 y1 z1, .xchg3 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpu x1 y1, .xcpu x2 y2 => x1 == x2 && y1 == y2
  | .xc2pu x1 y1 z1, .xc2pu x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpuxc x1 y1 z1, .xcpuxc x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .xcpu2 x1 y1 z1, .xcpu2 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .puxc2 x1 y1 z1, .puxc2 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .puxc x1 y1, .puxc x2 y2 => x1 == x2 && y1 == y2
  | .puxcpu x1 y1 z1, .puxcpu x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .push2 x1 y1, .push2 x2 y2 => x1 == x2 && y1 == y2
  | .push3 x1 y1 z1, .push3 x2 y2 z2 => x1 == x2 && y1 == y2 && z1 == z2
  | .blkSwap x1 y1, .blkSwap x2 y2 => x1 == x2 && y1 == y2
  | .rot, .rot => true
  | .rotRev, .rotRev => true
  | .twoSwap, .twoSwap => true
  | .twoOver, .twoOver => true
  | .reverse x1 y1, .reverse x2 y2 => x1 == x2 && y1 == y2
  | .tuck, .tuck => true
  | .pushCtr x, .pushCtr y => x == y
  | .popCtr x, .popCtr y => x == y
  | .setContCtr x, .setContCtr y => x == y
  | .ctos, .ctos => true
  | .xctos, .xctos => true
  | .newc, .newc => true
  | .endc, .endc => true
  | .ends, .ends => true
  | .ldu x, .ldu y => x == y
  | .loadInt ux px qx bx, .loadInt uy py qy by_ => ux == uy && px == py && qx == qy && bx == by_
  | .loadIntVar ux px qx, .loadIntVar uy py qy => ux == uy && px == py && qx == qy
  | .ldref, .ldref => true
  | .pldRefIdx x, .pldRefIdx y => x == y
  | .loadSliceX px qx, .loadSliceX py qy => px == py && qx == qy
  | .loadSliceFixed px qx bx, .loadSliceFixed py qy by_ => px == py && qx == qy && bx == by_
  | .sti x, .sti y => x == y
  | .stu x, .stu y => x == y
  | .stIntVar ux rx qx, .stIntVar uy ry qy => ux == uy && rx == ry && qx == qy
  | .stIntFixed ux rx qx bx, .stIntFixed uy ry qy by_ => ux == uy && rx == ry && qx == qy && bx == by_
  | .stSlice rx qx, .stSlice ry qy => rx == ry && qx == qy
  | .stSliceConst x, .stSliceConst y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .stZeroes, .stZeroes => true
  | .stOnes, .stOnes => true
  | .stSame, .stSame => true
  | .stref, .stref => true
  | .setcp x, .setcp y => x == y
  | .ifret, .ifret => true
  | .ifnotret, .ifnotret => true
  | .if_, .if_ => true
  | .ifnot, .ifnot => true
  | .inc, .inc => true
  | .dec, .dec => true
  | .negate, .negate => true
  | .add, .add => true
  | .sub, .sub => true
  | .subr, .subr => true
  | .mulInt x, .mulInt y => x == y
  | .mul, .mul => true
  | .min, .min => true
  | .max, .max => true
  | .minmax, .minmax => true
  | .mulShrModConst dx rx zx, .mulShrModConst dy ry zy => dx == dy && rx == ry && zx == zy
  | .divMod dx rx ax qx, .divMod dy ry ay qy => dx == dy && rx == ry && ax == ay && qx == qy
  | .lshiftConst qx bx, .lshiftConst qy by_ => qx == qy && bx == by_
  | .rshiftConst qx bx, .rshiftConst qy by_ => qx == qy && bx == by_
  | .equal, .equal => true
  | .neq, .neq => true
  | .throw x, .throw y => x == y
  | .throwIf x, .throwIf y => x == y
  | .throwIfNot x, .throwIfNot y => x == y
  | .throwAny p1 c1 t1, .throwAny p2 c2 t2 => p1 == p2 && c1 == c2 && t1 == t2
  | .saveCtr x, .saveCtr y => x == y
  | .sameAlt, .sameAlt => true
  | .sameAltSave, .sameAltSave => true
  | .dictPushConst dx nx, .dictPushConst dy ny => dx == dy && nx == ny
  | .dictGet ix ux rx, .dictGet iy uy ry => ix == iy && ux == uy && rx == ry
  | .dictGetExec ux cx zx, .dictGetExec uy cy zy => ux == uy && cx == cy && zx == zy
  | .dictSet ikx ukx rx mx, .dictSet iky uky ry my => ikx == iky && ukx == uky && rx == ry && mx == my
  | .dictReplaceB kx ux, .dictReplaceB ky uy => kx == ky && ux == uy
  | .stdict, .stdict => true
  | .skipdict, .skipdict => true
  | .lddict px qx, .lddict py qy => px == py && qx == qy
  | .and_, .and_ => true
  | .or, .or => true
  | .not_, .not_ => true
  | .sgn, .sgn => true
  | .less, .less => true
  | .leq, .leq => true
  | .greater, .greater => true
  | .geq, .geq => true
  | .cmp, .cmp => true
  | .sbits, .sbits => true
  | .srefs, .srefs => true
  | .sbitrefs, .sbitrefs => true
  | .sempty, .sempty => true
  | .sdempty, .sdempty => true
  | .srempty, .srempty => true
  | .sdCntTrail0, .sdCntTrail0 => true
  | .sdEq, .sdEq => true
  | .sdcutfirst, .sdcutfirst => true
  | .sdskipfirst, .sdskipfirst => true
  | .sdcutlast, .sdcutlast => true
  | .sdskiplast, .sdskiplast => true
  | .sdBeginsX qx, .sdBeginsX qy => qx == qy
  | .sdBeginsConst qx sx, .sdBeginsConst qy sy =>
      qx == qy && sx.bitPos == sy.bitPos && sx.refPos == sy.refPos && sx.cell == sy.cell
  | .lessInt x, .lessInt y => x == y
  | .eqInt x, .eqInt y => x == y
  | .gtInt x, .gtInt y => x == y
  | .neqInt x, .neqInt y => x == y
  | .pushNull, .pushNull => true
  | .isNull, .isNull => true
  | .nullSwapIfNot, .nullSwapIfNot => true
  | .mktuple x, .mktuple y => x == y
  | .index x, .index y => x == y
  | .untuple x, .untuple y => x == y
  | .blkdrop2 x1 y1, .blkdrop2 x2 y2 => x1 == x2 && y1 == y2
  | .pushSliceConst x, .pushSliceConst y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .pushCont x, .pushCont y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .execute, .execute => true
  | .jmpx, .jmpx => true
  | .callxArgs px rx, .callxArgs py ry => px == py && rx == ry
  | .jmpxArgs x, .jmpxArgs y => x == y
  | .ret, .ret => true
  | .retAlt, .retAlt => true
  | .retBool, .retBool => true
  | .retArgs x, .retArgs y => x == y
  | .ifjmp, .ifjmp => true
  | .ifnotjmp, .ifnotjmp => true
  | .ifelse, .ifelse => true
  | .ifref x, .ifref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifnotref x, .ifnotref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifjmpref x, .ifjmpref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifnotjmpref x, .ifnotjmpref y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifrefElse x, .ifrefElse y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifelseRef x, .ifelseRef y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .ifrefElseRef x1 y1, .ifrefElseRef x2 y2 =>
      x1.bitPos == x2.bitPos && x1.refPos == x2.refPos && x1.cell == x2.cell &&
      y1.bitPos == y2.bitPos && y1.refPos == y2.refPos && y1.cell == y2.cell
  | .callRef x, .callRef y => x.bitPos == y.bitPos && x.refPos == y.refPos && x.cell == y.cell
  | .callDict x, .callDict y => x == y
  | .while_, .while_ => true
  | .blkdrop x, .blkdrop y => x == y
  | .drop2, .drop2 => true
  | .balance, .balance => true
  | .now, .now => true
  | .getParam x, .getParam y => x == y
  | .randu256, .randu256 => true
  | .rand, .rand => true
  | .setRand x, .setRand y => x == y
  | .getGlobVar, .getGlobVar => true
  | .getGlob x, .getGlob y => x == y
  | .setGlobVar, .setGlobVar => true
  | .setGlob x, .setGlob y => x == y
  | .accept, .accept => true
  | .setGasLimit, .setGasLimit => true
  | .gasConsumed, .gasConsumed => true
  | .commit, .commit => true
  | .ldGrams, .ldGrams => true
  | .stGrams, .stGrams => true
  | .ldMsgAddr qx, .ldMsgAddr qy => qx == qy
  | .rewriteStdAddr qx, .rewriteStdAddr qy => qx == qy
  | .hashCU, .hashCU => true
  | .hashSU, .hashSU => true
  | .chkSignU, .chkSignU => true
  | .chkSignS, .chkSignS => true
  | .sendMsg, .sendMsg => true
  | .sendRawMsg, .sendRawMsg => true
  | .rawReserve, .rawReserve => true
  | _, _ => false⟩
-/

mutual
  structure OrdCregs where
    -- Minimal continuation control regs for MVP diff-testing.
    -- TVM allows SETCONTCTR for:
    -- - c0..c3 (continuations)
    -- - c4,c5 (data regs: cells)
    -- - c7 (tuple)
    --
    -- We currently need:
    -- - c0,c1 for BOOLAND/BOOLOR/COMPOSBOTH
    -- - c2 for TRY (exception handler chaining)
    -- - c4,c5,c7 for real-tx fixtures.
    c0 : Option Continuation := none
    c1 : Option Continuation := none
    c2 : Option Continuation := none
    c4 : Option Cell := none
    c5 : Option Cell := none
    c7 : Option (Array Value) := none
    deriving Repr

  structure OrdCdata where
    stack : Array Value := #[]
    nargs : Int := -1
    deriving Repr

  inductive Continuation : Type
    | ordinary (code : Slice) (savedC0 : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
    | quit (exitCode : Int)
    | excQuit
    | whileCond (cond : Continuation) (body : Continuation) (after : Continuation)
    | whileBody (cond : Continuation) (body : Continuation) (after : Continuation)
    | untilBody (body : Continuation) (after : Continuation)
    deriving Repr

  inductive Value : Type
    | int (i : IntVal)
    | cell (c : Cell)
    | slice (s : Slice)
    | builder (b : Builder)
    | tuple (t : Array Value)
    | cont (k : Continuation)
    | null
    deriving Repr
end

instance : Inhabited Value := ⟨.null⟩

def OrdCregs.empty : OrdCregs := {}

def OrdCdata.empty : OrdCdata := {}

def Value.pretty : Value → String
  | .int .nan => "NaN"
  | .int (.num n) => toString n
  | .null => "null"
  | .cell _ => "<cell>"
  | .slice _ => "<slice>"
  | .builder _ => "<builder>"
  | .tuple t => s!"<tuple:{t.size}>"
  | .cont k =>
      match k with
      | .ordinary _ _ _ _ => "<cont:ord>"
      | .quit n => s!"<cont:quit {n}>"
      | .excQuit => "<cont:excquit>"
      | .whileCond _ _ _ => "<cont:while-cond>"
      | .whileBody _ _ _ => "<cont:while-body>"
      | .untilBody _ _ => "<cont:until-body>"

instance : ToString Value := ⟨Value.pretty⟩

def arrayBeqBy {α : Type} (a b : Array α) (beq : α → α → Bool) : Bool :=
  if a.size != b.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:a.size] do
        match a.get? i, b.get? i with
        | some x, some y =>
            if !(beq x y) then
              ok := false
        | _, _ =>
            ok := false
      return ok

def arrayBeq {α : Type} [BEq α] (a b : Array α) : Bool :=
  arrayBeqBy a b (fun x y => x == y)

instance : BEq Slice := ⟨fun a b => a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell⟩
instance : BEq Builder := ⟨fun a b => a.bits == b.bits && arrayBeq a.refs b.refs⟩

partial def Continuation.beq : Continuation → Continuation → Bool
  | .quit x, .quit y => x == y
  | .excQuit, .excQuit => true
  | .ordinary x sx _ _, .ordinary y sy _ _ => x == y && Continuation.beq sx sy
  | .whileCond c1 b1 a1, .whileCond c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .whileBody c1 b1 a1, .whileBody c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | _, _ => false

instance : BEq Continuation := ⟨Continuation.beq⟩

partial def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .slice x, .slice y => x == y
  | .builder x, .builder y => x == y
  | .tuple x, .tuple y => arrayBeqBy x y Value.beq
  | .cont x, .cont y => x == y
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

abbrev Stack := Array Value

structure CallFrame where
  savedStack : Stack
  retArgs : Int
  deriving Repr

structure GasLimits where
  gasMax : Int
  gasLimit : Int
  gasCredit : Int
  gasRemaining : Int
  gasBase : Int
  deriving Repr

def GasLimits.infty : Int := (Int.ofNat (1 <<< 63)) - 1

def GasLimits.default : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := GasLimits.infty
    gasCredit := 0
    gasRemaining := GasLimits.infty
    gasBase := GasLimits.infty }

def GasLimits.ofLimit (limit : Int) : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := limit
    gasCredit := 0
    gasRemaining := limit
    gasBase := limit }

def GasLimits.gasConsumed (g : GasLimits) : Int :=
  g.gasBase - g.gasRemaining

def GasLimits.changeBase (g : GasLimits) (newBase : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining + (newBase - g.gasBase), gasBase := newBase }

def GasLimits.changeLimit (g : GasLimits) (newLimit : Int) : GasLimits :=
  let limit0 : Int := if newLimit < 0 then 0 else newLimit
  let limit : Int := if limit0 > g.gasMax then g.gasMax else limit0
  let g' : GasLimits := { g with gasCredit := 0, gasLimit := limit }
  g'.changeBase limit

def GasLimits.consume (g : GasLimits) (amount : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining - amount }

structure CommittedState where
  c4 : Cell
  c5 : Cell
  committed : Bool
  deriving Repr

def CommittedState.empty : CommittedState :=
  { c4 := Cell.empty, c5 := Cell.empty, committed := false }

def gasPerInstr : Int := 10
def exceptionGasPrice : Int := 50
def implicitJmpRefGasPrice : Int := 10
def implicitRetGasPrice : Int := 5
def cellLoadGasPrice : Int := 100
def cellReloadGasPrice : Int := 25
def cellCreateGasPrice : Int := 500
def tupleEntryGasPrice : Int := 1
def freeStackDepth : Nat := 32
def stackEntryGasPrice : Int := 1
def chksgnFreeCount : Nat := 10
def chksgnGasPrice : Int := 4000

def instrGas (i : Instr) (totBits : Nat) : Int :=
  let base : Int := gasPerInstr + Int.ofNat totBits
  match i with
  | .endc => base + cellCreateGasPrice
  -- `UNTIL`/loops in C++ allocate/attach a continuation envelope (`extract_cc`), which carries an extra fixed cost.
  | .until => base + 4
  | _ => base

/-! ### Minimal cp0 decoding (Milestone 2) -/

def Slice.takeBitsAsNat (s : Slice) (n : Nat) : Except Excno (Nat × Slice) := do
  if s.haveBits n then
    let bs := s.readBits n
    return (bitsToNat bs, s.advanceBits n)
  else
    throw .invOpcode

def Slice.peekBitsAsNat (s : Slice) (n : Nat) : Except Excno Nat := do
  if s.haveBits n then
    return bitsToNat (s.readBits n)
  else
    throw .invOpcode

def Slice.takeRefInv (s : Slice) : Except Excno (Cell × Slice) := do
  if s.haveRefs 1 then
    let c := s.cell.refs[s.refPos]!
    let s' := { s with refPos := s.refPos + 1 }
    return (c, s')
  else
    throw .invOpcode

def natToIntSignedTwos (n bits : Nat) : Int :=
  let half : Nat := 1 <<< (bits - 1)
  if n < half then
    Int.ofNat n
  else
    Int.ofNat n - Int.ofNat (1 <<< bits)

def bitsToIntSignedTwos (bs : BitString) : Int :=
  match bs.size with
  | 0 => 0
  | bits + 1 =>
      let u : Nat := bitsToNat bs
      if bs[0]! then
        Int.ofNat u - Int.ofNat (1 <<< (bits + 1))
      else
        Int.ofNat u

def decodeCp0WithBits (s : Slice) : Except Excno (Instr × Nat × Slice) := do
  -- PUSHINT (tinyint4): 4-bit prefix 0x7, 4-bit immediate.
  let p4 ← s.peekBitsAsNat 4
  if p4 = 0x7 then
    let (b8, s') ← s.takeBitsAsNat 8
    let imm4 : Nat := b8 &&& 0xf
    let x : Int := Int.ofNat ((imm4 + 5) &&& 0xf) - 5
    return (.pushInt (.num x), 8, s')

  -- PUSHCONT (tiny, 4-bit prefix 0x9): 4-bit prefix + 4-bit len (bytes), then that many bytes of inline code.
  if p4 = 0x9 then
    let (b8, s8) ← s.takeBitsAsNat 8
    let lenBytes : Nat := b8 &&& 0xf
    let dataBits : Nat := lenBytes * 8
    if !s8.haveBits dataBits then
      throw .invOpcode
    let codeBits := s8.readBits dataBits
    let rest := s8.advanceBits dataBits
    let codeCell : Cell := { bits := codeBits, refs := #[] }
    return (.pushCont (Slice.ofCell codeCell), 8, rest)

  -- Exception opcodes: THROW / THROWIF / THROWIFNOT short/long.
  -- Short: 10-bit prefix (0xf200 / 0xf240 / 0xf280 >> 6) + 6-bit excno.
  if s.haveBits 10 then
    let p10 := bitsToNat (s.readBits 10)
    if p10 = (0xf200 >>> 6) ∨ p10 = (0xf240 >>> 6) ∨ p10 = (0xf280 >>> 6) then
      let (_, s10) ← s.takeBitsAsNat 10
      let (exc, s16) ← s10.takeBitsAsNat 6
      let e : Int := Int.ofNat exc
      if p10 = (0xf200 >>> 6) then
        return (.throw e, 16, s16)
      else if p10 = (0xf240 >>> 6) then
        return (.throwIf e, 16, s16)
      else
        return (.throwIfNot e, 16, s16)
  -- Long: 13-bit prefix (0xf2c0 / 0xf2d0 / 0xf2e0 >> 3) + 11-bit excno.
  if s.haveBits 13 then
    let p13 := bitsToNat (s.readBits 13)
    if p13 = (0xf2c0 >>> 3) ∨ p13 = (0xf2d0 >>> 3) ∨ p13 = (0xf2e0 >>> 3) then
      let (_, s13) ← s.takeBitsAsNat 13
      let (exc, s24) ← s13.takeBitsAsNat 11
      let e : Int := Int.ofNat exc
      if p13 = (0xf2c0 >>> 3) then
        return (.throw e, 24, s24)
      else if p13 = (0xf2d0 >>> 3) then
        return (.throwIf e, 24, s24)
      else
        return (.throwIfNot e, 24, s24)

    -- SDBEGINS{Q} (const): 13-bit prefix (0xd728 >> 3) + 8-bit args + inline bits (args*8+3).
    if p13 = (0xd728 >>> 3) then
      if !s.haveBits 21 then
        throw .invOpcode
      let (_, s13) ← s.takeBitsAsNat 13
      let (args8, s21) ← s13.takeBitsAsNat 8
      let quiet : Bool := (args8 &&& 0x80) = 0x80
      let dataBits : Nat := (args8 &&& 0x7f) * 8 + 3
      if !s21.haveBits dataBits then
        throw .invOpcode
      let raw := s21.readBits dataBits
      let rest := s21.advanceBits dataBits
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := { bits, refs := #[] }
      return (.sdBeginsConst quiet (Slice.ofCell cell), 21, rest)

  -- DICTPUSHCONST (24-bit, +1 ref): 0xf4a4..0xf4a7 + 10-bit key size.
  if s.haveBits 24 then
    let w24 := bitsToNat (s.readBits 24)
    if 0xf4a400 ≤ w24 ∧ w24 < 0xf4a800 then
      if !s.haveRefs 1 then
        throw .invOpcode
      -- Layout (pfx_bits=24):
      --   advance 13; take 1 bit (maybe), take 1 ref; take 10-bit n.
      let (_, s13) ← s.takeBitsAsNat 13
      let (_, s14) ← s13.takeBitsAsNat 1
      let (dictCell, sRef) ← s14.takeRefInv
      let (n, s24) ← sRef.takeBitsAsNat 10
      return (.dictPushConst dictCell n, 24, s24)

    -- {P}LDSLICE{Q} <bits> (24-bit): 14-bit prefix (0xd71c >> 2) + 10-bit args (flags2 + bits8).
    -- Matches C++ `exec_load_slice_fixed2`.
    let p14 := w24 >>> 10
    if p14 = (0xd71c >>> 2) then
      let args10 : Nat := w24 &&& 0x3ff
      let flags2 : Nat := args10 >>> 8
      let bits : Nat := (args10 &&& 0xff) + 1
      let prefetch : Bool := (flags2 &&& 1) = 1
      let quiet : Bool := (flags2 &&& 2) = 2
      let (_, s24) ← s.takeBitsAsNat 24
      return (.loadSliceFixed prefetch quiet bits, 24, s24)

    -- QLSHIFT / QRSHIFT (24-bit): 16-bit opcode 0xb7aa/0xb7ab + 8-bit arg.
    let p16 := w24 >>> 8
    if p16 = 0xb7aa then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.lshiftConst true bits, 24, s24)
    if p16 = 0xb7ab then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.rshiftConst true bits, 24, s24)

    -- QDIV/MOD family (24-bit): 20-bit prefix 0xb7a90 + 4-bit args.
    let p20 := w24 >>> 4
    if p20 = 0xb7a90 then
      let args4 : Nat := w24 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.divMod d roundMode add true, 24, s24)

    -- Integer load from slice: 13-bit prefix (0xd708 >> 3) + 11-bit args.
    -- Matches C++ `exec_load_int_fixed2`.
    let p13 := w24 >>> 11
    if p13 = (0xd708 >>> 3) then
      let args11 : Nat := w24 &&& 0x7ff
      let flags3 : Nat := args11 >>> 8
      let bits : Nat := (args11 &&& 0xff) + 1
      let unsigned : Bool := (flags3 &&& 1) = 1
      let prefetch : Bool := (flags3 &&& 2) = 2
      let quiet : Bool := (flags3 &&& 4) = 4
      let (_, s24) ← s.takeBitsAsNat 24
      return (.loadInt unsigned prefetch quiet bits, 24, s24)

    -- ST{I,U}{R}{Q} <bits> (24-bit): 13-bit prefix (0xcf08 >> 3) + 11-bit args (flags3 + bits8).
    -- Matches C++ `exec_store_int_fixed`.
    if p13 = (0xcf08 >>> 3) then
      let args11 : Nat := w24 &&& 0x7ff
      let flags3 : Nat := args11 >>> 8
      let bits : Nat := (args11 &&& 0xff) + 1
      let unsigned : Bool := (flags3 &&& 1) = 1
      let rev : Bool := (flags3 &&& 2) = 2
      let quiet : Bool := (flags3 &&& 4) = 4
      let (_, s24) ← s.takeBitsAsNat 24
      return (.stIntFixed unsigned rev quiet bits, 24, s24)

    -- XC2PU: 12-bit prefix 0x541 + 12-bit args (x,y,z nibbles).
    let p12 := w24 >>> 12
    if p12 = 0x540 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xchg3 x y z, 24, s24)
    if p12 = 0x541 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xc2pu x y z, 24, s24)
    if p12 = 0x542 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xcpuxc x y z, 24, s24)
    if p12 = 0x543 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xcpu2 x y z, 24, s24)
    if p12 = 0x544 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.puxc2 x y z, 24, s24)
    if p12 = 0x545 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.puxcpu x y z, 24, s24)
    if p12 = 0x547 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.push3 x y z, 24, s24)

    -- MUL{RSHIFT,MODPOW2,RSHIFTMOD}# (24-bit): 12-bit prefix 0xa9b + 12-bit args (cfg4 + z8).
    if p12 = 0xa9b then
      let args12 : Nat := w24 &&& 0xfff
      let cfg4 : Nat := args12 >>> 8
      let z : Nat := (args12 &&& 0xff) + 1
      let roundMode : Int := Int.ofNat (cfg4 &&& 0x3) - 1
      let d : Nat := (cfg4 >>> 2) &&& 0x3
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.mulShrModConst d roundMode z, 24, s24)

  -- PUSHCONT (general, 7-bit prefix 0x47): 7-bit prefix + 9-bit args + inline bits + inline refs.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    let p7 := w16 >>> 9
    if p7 = 0x47 then
      let args9 : Nat := w16 &&& 0x1ff
      let refs : Nat := (args9 >>> 7) &&& 0x3
      let lenBytes : Nat := args9 &&& 0x7f
      let dataBits : Nat := lenBytes * 8
      if !s.haveBits (16 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      let codeBits := s16.readBits dataBits
      let mut rest := s16.advanceBits dataBits
      let mut contRefs : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        contRefs := contRefs.push c
        rest := rest'
      let codeCell : Cell := { bits := codeBits, refs := contRefs }
      return (.pushCont (Slice.ofCell codeCell), 16, rest)

  -- PUSHSLICE r2 (18-bit prefix): 0x8d + 3-bit refs (0..4) + 7-bit len, then inline bits/refs.
  -- Matches C++ `exec_push_slice_r2`.
  if s.haveBits 18 then
    let w18 := bitsToNat (s.readBits 18)
    if w18 >>> 10 = 0x8d then
      let refs : Nat := (w18 >>> 7) &&& 0x7
      if refs > 4 then
        throw .invOpcode
      let len7 : Nat := w18 &&& 0x7f
      let dataBits : Nat := len7 * 8 + 6
      if !s.haveBits (18 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s18) ← s.takeBitsAsNat 18
      let raw := s18.readBits dataBits
      let mut rest := s18.advanceBits dataBits
      let mut refCells : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        refCells := refCells.push c
        rest := rest'
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := { bits, refs := refCells }
      return (.pushSliceConst (Slice.ofCell cell), 18, rest)

  -- PUSHINT (8/16/long)
  -- STSLICECONST (inline constant slice): 9-bit prefix 0xcf80>>7 + 5-bit args, then inline slice bits/refs.
  if s.haveBits 14 then
    let w14 := bitsToNat (s.readBits 14)
    if w14 >>> 5 = (0xcf80 >>> 7) then
      let args5 : Nat := w14 &&& 0x1f
      let refs : Nat := (args5 >>> 3) &&& 0x3
      let dataBits : Nat := (args5 &&& 0x7) * 8 + 2
      if !s.haveBits (14 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s14) ← s.takeBitsAsNat 14
      let raw := s14.readBits dataBits
      let mut rest := s14.advanceBits dataBits
      let mut rs : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        rs := rs.push c
        rest := rest'
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := { bits, refs := rs }
      return (.stSliceConst (Slice.ofCell cell), 14, rest)

  let b8 ← s.peekBitsAsNat 8
  -- PUSHREFCONT: 0x8a (8) + 1 ref.
  if b8 = 0x8a then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRefCont c, 8, s')
  -- PUSHSLICE (const): 0x8b (8) + 4-bit args, then inline bits (args*8+4); strip trailing marker.
  if b8 = 0x8b then
    if !s.haveBits 12 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (args4, s12) ← s8.takeBitsAsNat 4
    let dataBits : Nat := (args4 &&& 0xf) * 8 + 4
    if !s12.haveBits dataBits then
      throw .invOpcode
    let raw := s12.readBits dataBits
    let rest := s12.advanceBits dataBits
    let bits := bitsStripTrailingMarker raw
    let cell : Cell := { bits, refs := #[] }
    return (.pushSliceConst (Slice.ofCell cell), 12, rest)
  if b8 = 0x80 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.pushInt (.num (natToIntSignedTwos arg 8)), 16, s16)
  if b8 = 0x81 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s24) ← s8.takeBitsAsNat 16
    return (.pushInt (.num (natToIntSignedTwos arg 16)), 24, s24)
  if b8 = 0x82 then
    -- Extended constant: 0x82 (8) + len (5) + value (3 + 8*(len+2)).
    if !s.haveBits 13 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (len5, s13) ← s8.takeBitsAsNat 5
    let l : Nat := len5 + 2
    let width : Nat := 3 + l * 8
    if !s13.haveBits width then
      throw .invOpcode
    let bs := s13.readBits width
    let s' := s13.advanceBits width
    return (.pushInt (.num (bitsToIntSignedTwos bs)), 13, s')

  -- 16-bit control register ops: PUSH c<i>, POP c<i>.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    -- ST{I,U}X{R}{Q}: 0xcf00..0xcf07 (16-bit; 13-bit prefix + 3-bit flags).
    if w16 &&& 0xfff8 = 0xcf00 then
      let args3 : Nat := w16 &&& 0x7
      let unsigned : Bool := (args3 &&& 1) = 1
      let rev : Bool := (args3 &&& 2) = 2
      let quiet : Bool := (args3 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stIntVar unsigned rev quiet, 16, s16)
    if w16 = 0xcf31 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bbits, 16, s16)
    -- THROW{ARG}ANY{IF,IFNOT}: 0xf2f0..0xf2f6 (16-bit, 3-bit args).
    if w16 &&& 0xfff8 = 0xf2f0 then
      let args3 : Nat := w16 &&& 0x7
      if args3 ≤ 6 then
        let hasParam : Bool := (args3 &&& 1) = 1
        let hasCond : Bool := (args3 &&& 6) ≠ 0
        let throwCond : Bool := (args3 &&& 2) = 2
        let (_, s16) ← s.takeBitsAsNat 16
        return (.throwAny hasParam hasCond throwCond, 16, s16)
    if w16 = 0xf2ff then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.try_, 16, s16)
    -- XCHG3 (16-bit): 4-bit prefix 0x4 + 12-bit args (x,y,z nibbles).
    if w16 >>> 12 = 0x4 then
      let args12 : Nat := w16 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.xchg3 x y z, 16, s16)
    -- BLKDROP (16-bit): 12-bit prefix 0x5f0 + 4-bit `n`.
    if w16 &&& 0xfff0 = 0x5f00 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkdrop n, 16, s16)
    -- BLKDROP2: 0x6c10..0x6cff (8-bit args packed as nibbles).
    if w16 &&& 0xff00 = 0x6c00 ∧ (w16 &&& 0xff) ≥ 0x10 then
      let args8 : Nat := w16 &&& 0xff
      let x : Nat := (args8 >>> 4) &&& 0xf
      let y : Nat := args8 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkdrop2 x y, 16, s16)
    -- TUPLE (12-bit prefix 0x6f0 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f00 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.mktuple n, 16, s16)
    -- INDEX (12-bit prefix 0x6f1 + 4-bit `i`).
    if w16 &&& 0xfff0 = 0x6f10 then
      let i : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.index i, 16, s16)
    -- UNTUPLE (12-bit prefix 0x6f2 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f20 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.untuple n, 16, s16)
    if w16 = 0x6f8c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tpush, 16, s16)
    if w16 = 0x6fa1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIfNot, 16, s16)
    if w16 = 0xc700 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sempty, 16, s16)
    if w16 = 0xc701 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdempty, 16, s16)
    if w16 = 0xc702 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.srempty, 16, s16)
    if w16 = 0xc712 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdCntTrail0, 16, s16)
    if w16 = 0xc705 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdEq, 16, s16)
    if w16 = 0xd720 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdcutfirst, 16, s16)
    if w16 = 0xd721 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdskipfirst, 16, s16)
    if w16 = 0xd722 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdcutlast, 16, s16)
    if w16 = 0xd723 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdskiplast, 16, s16)
    if w16 = 0xb608 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.min, 16, s16)
    if w16 = 0xb609 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.max, 16, s16)
    if w16 = 0xb60a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.minmax, 16, s16)
    -- PUSHPOW2 / PUSHNAN: 0x8300..0x83ff.
    if w16 &&& 0xff00 = 0x8300 then
      let (_, s16) ← s.takeBitsAsNat 16
      if w16 = 0x83ff then
        return (.pushInt .nan, 16, s16)
      else
        let exp : Nat := (w16 &&& 0xff) + 1
        return (.pushPow2 exp, 16, s16)
    -- {PLD,LD}{I,U}X{Q}: 0xd700..0xd707 (13-bit prefix + 3-bit args).
    if w16 &&& 0xfff8 = 0xd700 then
      let args3 : Nat := w16 &&& 0x7
      let unsigned : Bool := (args3 &&& 1) = 1
      let prefetch : Bool := (args3 &&& 2) = 2
      let quiet : Bool := (args3 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadIntVar unsigned prefetch quiet, 16, s16)
    -- {PLD,LD}SLICEX{Q}: 0xd718..0xd71b (14-bit prefix + 2-bit args).
    if w16 &&& 0xfffc = 0xd718 then
      let args2 : Nat := w16 &&& 0x3
      let prefetch : Bool := (args2 &&& 1) = 1
      let quiet : Bool := (args2 &&& 2) = 2
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadSliceX prefetch quiet, 16, s16)
    -- DIV/MOD family (16-bit): 12-bit prefix 0xa90 + 4-bit args.
    if w16 >>> 4 = 0xa90 then
      let args4 : Nat := w16 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.divMod d roundMode add false, 16, s16)
    -- Store slice into builder (16-bit): STSLICE / STSLICER and quiet variants.
    if w16 = 0xcf12 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false false, 16, s16)
    if w16 = 0xcf16 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true false, 16, s16)
    if w16 = 0xcf1a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false true, 16, s16)
    if w16 = 0xcf1e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true true, 16, s16)
    if w16 = 0xcf40 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stZeroes, 16, s16)
    if w16 = 0xcf41 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stOnes, 16, s16)
    if w16 = 0xcf42 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSame, 16, s16)
    if w16 &&& 0xff00 = 0xf000 then
      let idx : Nat := w16 &&& 0xff
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callDict idx, 16, s16)
    if w16 = 0xf800 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.accept, 16, s16)
    if w16 = 0xf801 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setGasLimit, 16, s16)
    if w16 = 0xf810 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.randu256, 16, s16)
    if w16 = 0xf811 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.rand, 16, s16)
    if w16 = 0xf807 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.gasConsumed, 16, s16)
    if w16 = 0xf80f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.commit, 16, s16)
    if w16 = 0xf823 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.now, 16, s16)
    if w16 = 0xf827 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.balance, 16, s16)
    if w16 = 0xf814 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setRand false, 16, s16)
    if w16 = 0xf815 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setRand true, 16, s16)
    if 0xf820 ≤ w16 ∧ w16 ≤ 0xf82f then
      let idx : Nat := w16 - 0xf820
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getParam idx, 16, s16)
    if w16 = 0xf840 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getGlobVar, 16, s16)
    if 0xf841 ≤ w16 ∧ w16 < 0xf860 then
      -- C++ `GETGLOB` immediate uses low 5 bits; the range 0xf841..0xf85f corresponds to 1..31.
      let idx : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getGlob idx, 16, s16)
    if w16 = 0xf860 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setGlobVar, 16, s16)
    if 0xf861 ≤ w16 ∧ w16 < 0xf880 then
      -- C++ `SETGLOB` immediate uses low 5 bits; the range 0xf861..0xf87f corresponds to 1..31.
      let idx : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setGlob idx, 16, s16)
    if w16 = 0xf900 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.hashCU, 16, s16)
    if w16 = 0xf901 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.hashSU, 16, s16)
    if w16 = 0xf910 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.chkSignU, 16, s16)
    if w16 = 0xf911 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.chkSignS, 16, s16)
    if w16 = 0xed11 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setContVarArgs, 16, s16)
    if w16 &&& 0xfff8 = 0xed40 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.pushCtr idx, 16, s16)
    if w16 &&& 0xfff8 = 0xed50 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.popCtr idx, 16, s16)
    if w16 &&& 0xfff0 = 0xed60 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 ∨ idx ≥ 8 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setContCtr idx, 16, s16)
    if w16 &&& 0xfff8 = 0xeda0 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.saveCtr idx, 16, s16)
    if w16 = 0xedf0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.boolAnd, 16, s16)
    if w16 = 0xedf1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.boolOr, 16, s16)
    if w16 = 0xedf2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.composBoth, 16, s16)
    if w16 = 0xedfa then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sameAlt, 16, s16)
    if w16 = 0xedfb then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sameAltSave, 16, s16)
    if w16 &&& 0xff00 = 0xff00 then
      let b : Nat := w16 &&& 0xff
      if b = 0xf0 then
        throw .invOpcode
      -- Match `exec_set_cp`: cp = ((b + 0x10) & 0xff) - 0x10.
      let cp : Int := Int.ofNat ((b + 0x10) &&& 0xff) - 0x10
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setcp cp, 16, s16)

    if w16 = 0xfa00 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ldGrams, 16, s16)
    if w16 = 0xfa02 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stGrams, 16, s16)
    if w16 = 0xfa40 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ldMsgAddr false, 16, s16)
    if w16 = 0xfa41 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ldMsgAddr true, 16, s16)
    if w16 = 0xfa44 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.rewriteStdAddr false, 16, s16)
    if w16 = 0xfa45 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.rewriteStdAddr true, 16, s16)
    if w16 = 0xfb00 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sendRawMsg, 16, s16)
    if w16 = 0xfb02 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.rawReserve, 16, s16)
    if w16 = 0xfb08 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sendMsg, 16, s16)

    if w16 = 0xe302 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifjmpref (Slice.ofCell c) , 16, rest)
    if w16 = 0xe303 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifnotjmpref (Slice.ofCell c), 16, rest)
    if w16 = 0xe300 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifref (Slice.ofCell c), 16, rest)
    if w16 = 0xe301 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifnotref (Slice.ofCell c), 16, rest)
    if w16 = 0xe30d then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifrefElse (Slice.ofCell c), 16, rest)
    if w16 = 0xe30e then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifelseRef (Slice.ofCell c), 16, rest)
    if w16 = 0xe30f then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c1, s1) ← s16.takeRefInv
      let (c2, rest) ← s1.takeRefInv
      return (.ifrefElseRef (Slice.ofCell c1) (Slice.ofCell c2), 16, rest)

    -- Continuation calls/jumps with arg counts (contops.cpp).
    -- CALLXARGS <params>,<retvals>: 0xda (8-bit) + args8 (params:4, retvals:4).
    if w16 &&& 0xff00 = 0xda00 then
      let args8 : Nat := w16 &&& 0xff
      let params : Nat := (args8 >>> 4) &&& 0xf
      let retVals : Int := Int.ofNat (args8 &&& 0xf)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callxArgs params retVals, 16, s16)
    -- CALLXARGS <params>,-1: 12-bit prefix 0xdb0 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb00 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callxArgs params (-1), 16, s16)
    -- JMPXARGS <params>: 12-bit prefix 0xdb1 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb10 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.jmpxArgs params, 16, s16)
    -- RETARGS <params>: 12-bit prefix 0xdb2 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb20 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retArgs params, 16, s16)
    if w16 = 0xdb30 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ret, 16, s16)
    if w16 = 0xdb31 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retAlt, 16, s16)
    if w16 = 0xdb32 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retBool, 16, s16)
    if w16 = 0xdb3c then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.callRef (Slice.ofCell c), 16, rest)

    if w16 = 0xf400 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stdict, 16, s16)
    if w16 = 0xf401 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.skipdict, 16, s16)
    -- DICT{I,U}GET{REF?}: 0xf40a..0xf40f.
    if 0xf40a ≤ w16 ∧ w16 ≤ 0xf40f then
      let byRef : Bool := (w16 &&& 1) = 1
      let intKey : Bool := (w16 &&& 4) = 4
      let unsigned : Bool := intKey && ((w16 &&& 2) = 2)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGet intKey unsigned byRef, 16, s16)

    -- DICT{I,U}{SET,REPLACE,ADD}{REF?}: 0xf412..0xf417 / 0xf422..0xf427 / 0xf432..0xf437.
    let decodeDictSet (mode : DictSetMode) : Except Excno (Instr × Nat × Slice) := do
      let byRef : Bool := (w16 &&& 1) = 1
      let intKey : Bool := (w16 &&& 4) = 4
      let unsigned : Bool := intKey && ((w16 &&& 2) = 2)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictSet intKey unsigned byRef mode, 16, s16)
    if 0xf412 ≤ w16 ∧ w16 < 0xf418 then
      return (← decodeDictSet .set)
    if 0xf422 ≤ w16 ∧ w16 < 0xf428 then
      return (← decodeDictSet .replace)
    if 0xf432 ≤ w16 ∧ w16 < 0xf438 then
      return (← decodeDictSet .add)

    -- DICT{I,U}?REPLACEB (builder value): 0xf449..0xf44b.
    if 0xf449 ≤ w16 ∧ w16 < 0xf44c then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictReplaceB intKey unsigned, 16, s16)

    if w16 = 0xd726 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdBeginsX false, 16, s16)
    if w16 = 0xd727 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdBeginsX true, 16, s16)

    -- DICT{I,U}GET{JMP,EXEC}{Z}: 0xf4a0..0xf4a3 (no Z) and 0xf4bc..0xf4bf (Z).
    if w16 &&& 0xfffc = 0xf4a0 ∨ w16 &&& 0xfffc = 0xf4bc then
      let unsigned : Bool := (w16 &&& 1) = 1
      let doCall : Bool := (w16 &&& 2) = 2
      let pushZ : Bool := (w16 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetExec unsigned doCall pushZ, 16, s16)

    -- {P}LDDICT{Q}: 0xf404..0xf407.
    if w16 &&& 0xfffc = 0xf404 then
      let args2 : Nat := w16 &&& 0x3
      let preload : Bool := (args2 &&& 1) = 1
      let quiet : Bool := (args2 &&& 2) = 2
      let (_, s16) ← s.takeBitsAsNat 16
      return (.lddict preload quiet, 16, s16)

    if w16 = 0xd739 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.xctos, 16, s16)
    if w16 = 0xd749 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sbits, 16, s16)
    if w16 = 0xd74a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.srefs, 16, s16)
    if w16 = 0xd74b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sbitrefs, 16, s16)
    if w16 &&& 0xfffc = 0xd74c then
      let idx : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.pldRefIdx idx, 16, s16)

  -- 8-bit opcodes / fixed+arg opcodes
  if b8 = 0x00 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.nop, 8, s')
  if b8 = 0x84 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let exp : Nat := (args &&& 0xff) + 1
    return (.pushPow2Dec exp, 16, s16)
  if b8 = 0x85 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let exp : Nat := (args &&& 0xff) + 1
    return (.pushNegPow2 exp, 16, s16)
  if b8 = 0x01 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 1, 8, s')
  if 0x02 ≤ b8 ∧ b8 ≤ 0x0f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 idx, 8, s')
  if b8 = 0x10 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xchg x y, 16, s16)
  if b8 = 0x11 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.xchg0 idx, 16, s16)
  if 0x12 ≤ b8 ∧ b8 ≤ 0x1f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg1 idx, 8, s')
  if b8 = 0x20 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 0, 8, s')
  if b8 = 0x21 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 1, 8, s')
  if 0x22 ≤ b8 ∧ b8 ≤ 0x2f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.push idx, 8, s')
  if b8 = 0x30 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 0, 8, s')
  if b8 = 0x31 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 1, 8, s')
  if 0x32 ≤ b8 ∧ b8 ≤ 0x3f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop idx, 8, s')
  if b8 = 0x50 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xchg2 x y, 16, s16)
  if b8 = 0x51 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xcpu x y, 16, s16)
  if b8 = 0x52 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.puxc x y, 16, s16)
  if b8 = 0x53 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.push2 x y, 16, s16)
  if b8 = 0x55 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := ((args >>> 4) &&& 0xf) + 1
    let y : Nat := (args &&& 0xf) + 1
    return (.blkSwap x y, 16, s16)
  if b8 = 0x56 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.push idx, 16, s16)
  if b8 = 0x57 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.pop idx, 16, s16)
  if b8 = 0x58 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rot, 8, s')
  if b8 = 0x59 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rotRev, 8, s')
  if b8 = 0x5a then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoSwap, 8, s')
  if b8 = 0x5b then
    let (_, s') ← s.takeBitsAsNat 8
    return (.drop2, 8, s')
  if b8 = 0x5d then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoOver, 8, s')
  if b8 = 0x5e then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := ((args >>> 4) &&& 0xf) + 2
    let y : Nat := args &&& 0xf
    return (.reverse x y, 16, s16)
  if b8 = 0x66 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.tuck, 8, s')
  if b8 = 0x6d then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pushNull, 8, s')
  if b8 = 0x6e then
    let (_, s') ← s.takeBitsAsNat 8
    return (.isNull, 8, s')
  if b8 = 0xa4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.inc, 8, s')
  if b8 = 0xa5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.dec, 8, s')
  if b8 = 0xa3 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.negate, 8, s')
  if b8 = 0xa0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.add, 8, s')
  if b8 = 0xa1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.sub, 8, s')
  if b8 = 0xa2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.subr, 8, s')
  if b8 = 0xa6 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.addInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xa7 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.mulInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xa8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.mul, 8, s')
  if b8 = 0xaa then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.lshiftConst false (arg + 1), 16, s16)
  if b8 = 0xab then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.rshiftConst false (arg + 1), 16, s16)
  if b8 = 0xac then
    let (_, s') ← s.takeBitsAsNat 8
    return (.lshift, 8, s')
  if b8 = 0xad then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rshift, 8, s')
  if b8 = 0xba then
    let (_, s') ← s.takeBitsAsNat 8
    return (.equal, 8, s')
  if b8 = 0xbd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.neq, 8, s')
  if b8 = 0xb0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.and_, 8, s')
  if b8 = 0xb1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.or, 8, s')
  if b8 = 0xb3 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.not_, 8, s')
  if b8 = 0xb8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.sgn, 8, s')
  if b8 = 0xb9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.less, 8, s')
  if b8 = 0xbb then
    let (_, s') ← s.takeBitsAsNat 8
    return (.leq, 8, s')
  if b8 = 0xbc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.greater, 8, s')
  if b8 = 0xbe then
    let (_, s') ← s.takeBitsAsNat 8
    return (.geq, 8, s')
  if b8 = 0xbf then
    let (_, s') ← s.takeBitsAsNat 8
    return (.cmp, 8, s')
  if b8 = 0xc0 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.eqInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc1 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.lessInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc2 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.gtInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc3 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.neqInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.newc, 8, s')
  if b8 = 0xc9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.endc, 8, s')
  if b8 = 0xca then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.sti (arg + 1), 16, s16)
  if b8 = 0xcb then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.stu (arg + 1), 16, s16)
  if b8 = 0xcc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.stref, 8, s')
  if b8 = 0xce then
    let (_, s') ← s.takeBitsAsNat 8
    return (.stSlice false false, 8, s')
  if b8 = 0xd0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ctos, 8, s')
  if b8 = 0xd1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ends, 8, s')
  if b8 = 0xd2 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.loadInt false false false (arg + 1), 16, s16)
  if b8 = 0xd3 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.ldu (arg + 1), 16, s16)
  if b8 = 0xd4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ldref, 8, s')
  if b8 = 0xd8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.execute, 8, s')
  if b8 = 0xd9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.jmpx, 8, s')
  if b8 = 0xdc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifret, 8, s')
  if b8 = 0xdd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnotret, 8, s')
  if b8 = 0xde then
    let (_, s') ← s.takeBitsAsNat 8
    return (.if_, 8, s')
  if b8 = 0xdf then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnot, 8, s')
  if b8 = 0xe0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifjmp, 8, s')
  if b8 = 0xe1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnotjmp, 8, s')
  if b8 = 0xe2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifelse, 8, s')
  if b8 = 0xe6 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.until, 8, s')
  if b8 = 0xe8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.while_, 8, s')

  throw .invOpcode

def decodeCp0 (s : Slice) : Except Excno (Instr × Slice) := do
  let (i, _, rest) ← decodeCp0WithBits s
  return (i, rest)

def intToBitsTwos (n : Int) (bits : Nat) : Except Excno BitString := do
  if bits = 0 then
    return #[]
  -- For signed `bits`-wide two's complement, require `-(2^(bits-1)) ≤ n < 2^(bits-1)`.
  let half : Int := intPow2 (bits - 1)
  if decide (n < -half ∨ n ≥ half) then
    throw .rangeChk
  let modulus : Nat := 1 <<< bits
  if n ≥ 0 then
    let u := n.toNat
    return natToBits u bits
  else
    -- two's complement: 2^bits - |n|
    let abs : Nat := (-n).toNat
    return natToBits (modulus - abs) bits

def Slice.takeBitsAsNatCellUnd (s : Slice) (n : Nat) : Except Excno (Nat × Slice) := do
  if s.haveBits n then
    let bs := s.readBits n
    return (bitsToNat bs, s.advanceBits n)
  else
    throw .cellUnd

def Slice.skipMaybeAnycast (s : Slice) : Except Excno Slice := do
  -- Minimal support: accept `nothing$0` and reject `just$1` (Anycast).
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return s1
  else
    throw .cellUnd

def Slice.skipMessageAddr (s : Slice) : Except Excno Slice := do
  -- Minimal `MsgAddress` support (enough for common std addresses used in real txs).
  let (tag, s2) ← s.takeBitsAsNatCellUnd 2
  match tag with
  | 0 =>
      -- addr_none$00
      return s2
  | 1 =>
      -- addr_extern$01 len:(## 9) external_address:(bits len)
      let (len, s11) ← s2.takeBitsAsNatCellUnd 9
      if s11.haveBits len then
        return s11.advanceBits len
      else
        throw .cellUnd
  | 2 =>
      -- addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256
      let s3 ← s2.skipMaybeAnycast
      let need : Nat := 8 + 256
      if s3.haveBits need then
        return s3.advanceBits need
      else
        throw .cellUnd
  | 3 =>
      -- addr_var$11 (not needed for MVP txs yet)
      throw .cellUnd
  | _ =>
      throw .cellUnd

def Slice.prefixCell (start stop : Slice) : Cell :=
  { bits := start.cell.bits.extract start.bitPos stop.bitPos
    refs := start.cell.refs.extract start.refPos stop.refPos }

def natLenBits (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def Slice.countLeading (s : Slice) (b : Bool) : Nat :=
  Id.run do
    let mut k : Nat := 0
    while s.bitPos + k < s.cell.bits.size && s.cell.bits[s.bitPos + k]! == b do
      k := k + 1
    return k

structure DictLabel where
  remainder : Slice
  len : Nat
  sameBit : Option Bool
  storedBits : Nat
  deriving Repr

def parseDictLabel (cell : Cell) (maxLen : Nat) : Except Excno DictLabel := do
  let mut cs := Slice.ofCell cell
  if !cs.haveBits 2 then
    throw .cellUnd
  let p2 := bitsToNat (cs.readBits 2)
  match p2 with
  | 0 =>
      cs := cs.advanceBits 2
      return { remainder := cs, len := 0, sameBit := none, storedBits := 0 }
  | 1 =>
      -- hml_short: `0 1^len 0 <len bits>`
      cs := cs.advanceBits 1
      let lBits := cs.countLeading true
      if lBits > maxLen then
        throw .cellUnd
      if !cs.haveBits (2 * lBits + 1) then
        throw .cellUnd
      cs := cs.advanceBits (lBits + 1)
      return { remainder := cs, len := lBits, sameBit := none, storedBits := lBits }
  | 2 =>
      -- hml_long: `10 <lenBits bits len> <len bits>`
      let lenBits := natLenBits maxLen
      cs := cs.advanceBits 2
      let (lBits, cs') ← cs.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      if !cs'.haveBits lBits then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := none, storedBits := lBits }
  | 3 =>
      -- hml_same: `11b <lenBits bits len>`
      let lenBits := natLenBits maxLen
      if !cs.haveBits (3 + lenBits) then
        throw .cellUnd
      let (same3, cs3) ← cs.takeBitsAsNatCellUnd 3
      let sameBit := (same3 &&& 1) = 1
      let (lBits, cs') ← cs3.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := some sameBit, storedBits := 0 }
  | _ =>
      throw .cellUnd

def dictKeyBits? (idx : Int) (n : Nat) (unsigned : Bool) : Option BitString :=
  if n = 0 then
    if idx = 0 then some #[] else none
  else if unsigned then
    if idx < 0 then
      none
    else
      let u := idx.toNat
      if u ≥ (1 <<< n) then
        none
      else
        some (natToBits u n)
  else
    let half : Int := intPow2 (n - 1)
    if idx < -half ∨ idx ≥ half then
      none
    else
      match intToBitsTwos idx n with
      | .ok bs => some bs
      | .error _ => none

def dictLabelMatches (lbl : DictLabel) (key : BitString) (pos : Nat) : Bool :=
  if pos + lbl.len > key.size then
    false
  else
    match lbl.sameBit with
    | some b =>
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if key[pos + i]! != b then
              ok := false
          return ok
    | none =>
        let bs := lbl.remainder.readBits lbl.len
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if bs[i]! != key[pos + i]! then
              ok := false
          return ok

partial def dictLookupAux (cell : Cell) (key : BitString) (pos remaining : Nat) : Except Excno (Option Slice) := do
  let lbl ← parseDictLabel cell remaining
  if !dictLabelMatches lbl key pos then
    return none
  let rem0 : Nat := remaining - lbl.len
  if rem0 = 0 then
    return some (lbl.remainder.advanceBits lbl.storedBits)
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return none
    let sw : Bool := key[nextPos]!
    if !lbl.remainder.haveRefs 2 then
      throw .dictErr
    let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
    dictLookupAux child key (nextPos + 1) (rem0 - 1)

def dictLookup (root : Option Cell) (key : BitString) : Except Excno (Option Slice) := do
  match root with
  | none => return none
  | some cell =>
      dictLookupAux cell key 0 key.size

partial def dictLookupAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) :
    Except Excno (Option Slice × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  if !dictLabelMatches lbl key pos then
    return (none, #[cell])
  let rem0 : Nat := remaining - lbl.len
  if rem0 = 0 then
    return (some (lbl.remainder.advanceBits lbl.storedBits), #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return (none, #[cell])
    let sw : Bool := key[nextPos]!
    if !lbl.remainder.haveRefs 2 then
      throw .dictErr
    let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
    match (← dictLookupAuxWithCells child key (nextPos + 1) (rem0 - 1)) with
    | (res, cells) => return (res, #[cell] ++ cells)

def dictLookupWithCells (root : Option Cell) (key : BitString) : Except Excno (Option Slice × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      dictLookupAuxWithCells cell key 0 key.size

partial def dictReplaceBuilderAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) (newVal : Builder) :
    Except Excno (Cell × Bool × Nat × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  if !dictLabelMatches lbl key pos then
    return (cell, false, 0, #[cell])
  let rem0 : Nat := remaining - lbl.len
  if rem0 = 0 then
    let valueStart := lbl.remainder.advanceBits lbl.storedBits
    let prefixBits := cell.bits.take valueStart.bitPos
    let newBits := prefixBits ++ newVal.bits
    if newBits.size > 1023 || newVal.refs.size > 4 then
      throw .cellOv
    let newCell : Cell := { bits := newBits, refs := newVal.refs }
    return (newCell, true, 1, #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return (cell, false, 0, #[cell])
    let sw : Bool := key[nextPos]!
    if cell.refs.size < 2 then
      throw .dictErr
    let left := cell.refs[0]!
    let right := cell.refs[1]!
    let (childNew, ok, created, loaded) ←
      if sw then
        dictReplaceBuilderAuxWithCells right key (nextPos + 1) (rem0 - 1) newVal
      else
        dictReplaceBuilderAuxWithCells left key (nextPos + 1) (rem0 - 1) newVal
    if !ok then
      return (cell, false, 0, #[cell] ++ loaded)
    let newRefs : Array Cell :=
      if sw then
        #[left, childNew]
      else
        #[childNew, right]
    let newCell : Cell := { bits := cell.bits, refs := newRefs }
    return (newCell, true, created + 1, #[cell] ++ loaded)

def dictReplaceBuilderWithCells (root : Option Cell) (key : BitString) (newVal : Builder) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  match root with
  | none => return (none, false, 0, #[])
  | some cell =>
      let (c', ok, created, loaded) ← dictReplaceBuilderAuxWithCells cell key 0 key.size newVal
      return (some c', ok, created, loaded)

def bitsAllSame? (bs : BitString) : Option Bool :=
  if h : 0 < bs.size then
    let b0 := bs[0]!
    Id.run do
      let mut ok := true
      for i in [0:bs.size] do
        if bs[i]! != b0 then
          ok := false
      if ok then some b0 else none
  else
    none

def dictLabelEncodeSame (same : Bool) (len maxLen : Nat) : BitString :=
  let k : Nat := natLenBits maxLen
  if len > 1 && k < 2 * len - 1 then
    -- mode '11'
    natToBits (6 + (if same then 1 else 0)) 3 ++ natToBits len k
  else if k < len then
    -- mode '10'
    natToBits 2 2 ++ natToBits len k ++ Array.replicate len same
  else
    -- mode '0'
    #[false] ++ Array.replicate len true ++ #[false] ++ Array.replicate len same

def dictLabelEncode (labelBits : BitString) (len maxLen : Nat) : BitString :=
  if len = 0 then
    -- mode '0' with len=0: `0 0`
    #[false, false]
  else
    match bitsAllSame? (labelBits.take len) with
    | some b => dictLabelEncodeSame b len maxLen
    | none =>
        let k : Nat := natLenBits maxLen
        if k < len then
          -- mode '10'
          natToBits 2 2 ++ natToBits len k ++ labelBits.take len
        else
          -- mode '0'
          #[false] ++ Array.replicate len true ++ #[false] ++ labelBits.take len

def builderStoreBitsChecked (b : Builder) (bs : BitString) : Except Excno Builder := do
  if b.canExtendBy bs.size then
    return b.storeBits bs
  else
    throw .cellOv

def builderStoreRefChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy 0 1 then
    return { b with refs := b.refs.push c }
  else
    throw .cellOv

def builderAppendCellChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy c.bits.size c.refs.size then
    return { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
  else
    throw .cellOv

def dictCommonPrefixLen (lbl : DictLabel) (key : BitString) : Nat :=
  let l := lbl.len
  match lbl.sameBit with
  | some b =>
      Id.run do
        let mut k : Nat := 0
        while k < l && k < key.size && key[k]! == b do
          k := k + 1
        return k
  | none =>
      let bs := lbl.remainder.readBits l
      Id.run do
        let mut k : Nat := 0
        while k < l && k < key.size && bs[k]! == key[k]! do
          k := k + 1
        return k

partial def dictSetGenAuxWithCells (root : Option Cell) (key : BitString)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let n : Nat := key.size
  match root with
  | none =>
      if mode == .replace then
        return (none, false, 0, #[])
      let enc : BitString := dictLabelEncode key n n
      let b0 := Builder.empty
      let b1 ← builderStoreBitsChecked b0 enc
      let b2 ← storeVal b1
      return (some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel cell n
      let pfxLen : Nat := dictCommonPrefixLen lbl key
      if pfxLen < lbl.len then
        if mode == .replace then
          return (some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let m : Nat := n - pfxLen - 1
        let keySuffix : BitString := key.extract (pfxLen + 1) n

        -- New leaf for the inserted key.
        let enc1 : BitString := dictLabelEncode keySuffix m m
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← storeVal b1
        let cNew := b1.finalize

        -- Lower part of the old edge.
        let t : Nat := lbl.len - pfxLen - 1
        let oldLabelBits : BitString :=
          match lbl.sameBit with
          | some b => Array.replicate lbl.len b
          | none => lbl.remainder.readBits lbl.len
        let oldSuffix : BitString := oldLabelBits.extract (pfxLen + 1) lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t m
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        -- Fork node with the shared prefix.
        let prefBits : BitString := key.take pfxLen
        let encF : BitString := dictLabelEncode prefBits pfxLen n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let swBit : Bool := key[pfxLen]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (some bF.finalize, true, 3, #[cell])

      if lbl.len == n then
        -- Leaf node: key matches the whole label.
        if mode == .add then
          return (some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key n n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← storeVal b0
        return (some b0.finalize, true, 1, #[cell])

      -- Fork node: recurse into the selected child.
      if cell.refs.size < 2 then
        throw .dictErr
      let swBit : Bool := key[lbl.len]!
      let childKey : BitString := key.extract (lbl.len + 1) n
      let left0 := cell.refs[0]!
      let right0 := cell.refs[1]!
      if swBit then
        let (rightNew?, ok, created, loaded) ← dictSetGenAuxWithCells (some right0) childKey storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loaded)
        match rightNew? with
        | none => throw .dictErr
        | some rightNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b left0
            let b ← builderStoreRefChecked b rightNew
            return (some b.finalize, true, created + 1, #[cell] ++ loaded)
      else
        let (leftNew?, ok, created, loaded) ← dictSetGenAuxWithCells (some left0) childKey storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loaded)
        match leftNew? with
        | none => throw .dictErr
        | some leftNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b leftNew
            let b ← builderStoreRefChecked b right0
            return (some b.finalize, true, created + 1, #[cell] ++ loaded)

def dictSetRefWithCells (root : Option Cell) (key : BitString) (valRef : Cell) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderStoreRefChecked b valRef
  dictSetGenAuxWithCells root key storeVal mode

def dictSetSliceWithCells (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let c := val.toCellRemaining
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendCellChecked b c
  dictSetGenAuxWithCells root key storeVal mode

def bitsOr (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! || b[i.1]!

def bitsAnd (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! && b[i.1]!

def encodeCp0 (i : Instr) : Except Excno BitString := do
  match i with
  | .nop =>
      return natToBits 0x00 8
  | .pushInt .nan =>
      throw .invOpcode
  | .pushInt (.num n) =>
      if (-5 ≤ n ∧ n ≤ 10) then
        let imm : Nat :=
          if n ≥ 0 then
            n.toNat
          else
            (16 + n).toNat
        return natToBits (0x70 + imm) 8
      else if (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0x80 8 ++ natToBits imm 8
      else if (-32768 ≤ n ∧ n ≤ 32767) then
        let imm : Nat := if n ≥ 0 then n.toNat else (65536 - (-n).toNat)
        return natToBits 0x81 8 ++ natToBits imm 16
      else
        -- PUSHINT_LONG encoding (0x82 + len5 + value bits).
        -- For MVP assembly, pick the max width; it always decodes correctly and stays within 257-bit range checks.
        let len5 : Nat := 31
        let l := len5 + 2
        let width := 3 + l * 8
        let prefix13 : Nat := (0x82 <<< 5) + len5
        let valBits ← intToBitsTwos n width
        return natToBits prefix13 13 ++ valBits
  | .pushPow2 exp =>
      if 0 < exp ∧ exp ≤ 255 then
        return natToBits (0x8300 + (exp - 1)) 16
      else
        throw .rangeChk
  | .pushPow2Dec exp =>
      if 0 < exp ∧ exp ≤ 256 then
        return natToBits 0x84 8 ++ natToBits (exp - 1) 8
      else
        throw .rangeChk
  | .pushNegPow2 exp =>
      if 0 < exp ∧ exp ≤ 256 then
        return natToBits 0x85 8 ++ natToBits (exp - 1) 8
      else
        throw .rangeChk
  | .push idx =>
      if idx = 0 then
        return natToBits 0x20 8
      else if idx = 1 then
        return natToBits 0x21 8
      else if idx ≤ 15 then
        return natToBits (0x20 + idx) 8
      else if idx ≤ 255 then
        return natToBits 0x56 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .pop idx =>
      if idx = 0 then
        return natToBits 0x30 8
      else if idx = 1 then
        return natToBits 0x31 8
      else if idx ≤ 15 then
        return natToBits (0x30 + idx) 8
      else if idx ≤ 255 then
        return natToBits 0x57 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .xchg0 idx =>
      if idx = 0 then
        return natToBits 0x00 8
      else if idx = 1 then
        return natToBits 0x01 8
      else if idx ≤ 15 then
        return natToBits idx 8
      else if idx ≤ 255 then
        return natToBits 0x11 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .xchg1 idx =>
      if 2 ≤ idx ∧ idx ≤ 15 then
        return natToBits (0x10 + idx) 8
      else
        throw .rangeChk
  | .xchg x y =>
      if x ≤ 15 ∧ y ≤ 15 ∧ 0 < x ∧ x < y then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x10 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xchg2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x50 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xchg3 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        return natToBits (0x4000 + args) 16
      else
        throw .rangeChk
  | .xcpu x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x51 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xc2pu x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x541 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .xcpuxc x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x542 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .xcpu2 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x543 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .puxc2 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x544 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .puxc x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x52 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .puxcpu x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x545 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .push2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x53 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .push3 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x547 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .blkSwap x y =>
      if 1 ≤ x ∧ x ≤ 16 ∧ 1 ≤ y ∧ y ≤ 16 then
        let args : Nat := ((x - 1) <<< 4) + (y - 1)
        return natToBits 0x55 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .rot =>
      return natToBits 0x58 8
  | .rotRev =>
      return natToBits 0x59 8
  | .twoSwap =>
      return natToBits 0x5a 8
  | .twoOver =>
      return natToBits 0x5d 8
  | .reverse x y =>
      if 2 ≤ x ∧ x ≤ 17 ∧ y ≤ 15 then
        let args : Nat := ((x - 2) <<< 4) + y
        return natToBits 0x5e 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .tuck =>
      return natToBits 0x66 8
  | .pushCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed40 + idx) 16
  | .popCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed50 + idx) 16
  | .setContCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed60 + idx) 16
  | .saveCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xeda0 + idx) 16
  | .sameAlt =>
      return natToBits 0xedfa 16
  | .sameAltSave =>
      return natToBits 0xedfb 16
  | .boolAnd =>
      return natToBits 0xedf0 16
  | .boolOr =>
      return natToBits 0xedf1 16
  | .composBoth =>
      return natToBits 0xedf2 16
  | .setContVarArgs =>
      return natToBits 0xed11 16
  | .ctos =>
      return natToBits 0xd0 8
  | .xctos =>
      return natToBits 0xd739 16
  | .newc =>
      return natToBits 0xc8 8
  | .endc =>
      return natToBits 0xc9 8
  | .ends =>
      return natToBits 0xd1 8
  | .ldu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xd3 8 ++ natToBits (bits - 1) 8
  | .loadInt _ _ _ _ =>
      throw .invOpcode
  | .loadIntVar unsigned prefetch quiet =>
      let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
      return natToBits (0xd700 + args3) 16
  | .ldref =>
      return natToBits 0xd4 8
  | .pldRefIdx idx =>
      if idx < 4 then
        return natToBits (0xd74c + idx) 16
      else
        throw .rangeChk
  | .loadSliceX prefetch quiet =>
      let args : Nat := (if prefetch then 1 else 0) + (if quiet then 2 else 0)
      return natToBits (0xd718 + args) 16
  | .loadSliceFixed prefetch quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let bits8 : Nat := bits - 1
      let flags2 : Nat := (if prefetch then 1 else 0) + (if quiet then 2 else 0)
      let args10 : Nat := (flags2 <<< 8) + bits8
      let prefix14 : Nat := (0xd71c >>> 2)
      let word24 : Nat := (prefix14 <<< 10) + args10
      return natToBits word24 24
  | .sti bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xca 8 ++ natToBits (bits - 1) 8
  | .stu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xcb 8 ++ natToBits (bits - 1) 8
  | .stIntVar unsigned rev quiet =>
      let args3 : Nat := (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
      return natToBits (0xcf00 + args3) 16
  | .stIntFixed unsigned rev quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let bits8 : Nat := bits - 1
      let flags3 : Nat := (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
      let args11 : Nat := (flags3 <<< 8) + bits8
      let prefix13 : Nat := (0xcf08 >>> 3)
      let word24 : Nat := (prefix13 <<< 11) + args11
      return natToBits word24 24
  | .stSlice rev quiet =>
      if !rev && !quiet then
        return natToBits 0xce 8
      else if rev && !quiet then
        return natToBits 0xcf16 16
      else if !rev && quiet then
        return natToBits 0xcf1a 16
      else
        return natToBits 0xcf1e 16
  | .stSliceConst _ =>
      throw .invOpcode
  | .stZeroes =>
      return natToBits 0xcf40 16
  | .stOnes =>
      return natToBits 0xcf41 16
  | .stSame =>
      return natToBits 0xcf42 16
  | .stref =>
      return natToBits 0xcc 8
  | .bbits =>
      return natToBits 0xcf31 16
  | .setcp cp =>
      -- Encode only the immediate SETCP form (no SETCPX), matching C++ `exec_set_cp`.
      if cp = -16 then throw .invOpcode
      if decide (-15 ≤ cp ∧ cp ≤ 239) then
        let b : Nat :=
          if cp ≥ 0 then
            cp.toNat
          else
            (256 + cp).toNat
        return natToBits 0xff 8 ++ natToBits b 8
      else
        throw .invOpcode
  | .ifret =>
      return natToBits 0xdc 8
  | .ifnotret =>
      return natToBits 0xdd 8
  | .if_ =>
      return natToBits 0xde 8
  | .ifnot =>
      return natToBits 0xdf 8
  | .negate =>
      return natToBits 0xa3 8
  | .inc =>
      return natToBits 0xa4 8
  | .dec =>
      return natToBits 0xa5 8
  | .add =>
      return natToBits 0xa0 8
  | .addInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xa6 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .sub =>
      return natToBits 0xa1 8
  | .subr =>
      return natToBits 0xa2 8
  | .mulInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xa7 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .mul =>
      return natToBits 0xa8 8
  | .min =>
      return natToBits 0xb608 16
  | .max =>
      return natToBits 0xb609 16
  | .minmax =>
      return natToBits 0xb60a 16
  | .mulShrModConst _ _ _ =>
      throw .invOpcode
  | .divMod d roundMode addMode quiet =>
      let roundEnc : Int := roundMode + 1
      if roundEnc < 0 ∨ roundEnc > 2 then
        throw .rangeChk
      if d = 0 ∨ d > 3 then
        throw .rangeChk
      if addMode && (d != 3) then
        throw .rangeChk
      let dEnc : Nat := if addMode then 0 else d
      let args4 : Nat := (dEnc <<< 2) + roundEnc.toNat
      if quiet then
        let word24 : Nat := (0xb7a90 <<< 4) + args4
        return natToBits word24 24
      else
        return natToBits (0xa900 + args4) 16
  | .lshiftConst quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let imm : Nat := bits - 1
      if quiet then
        return natToBits 0xb7aa 16 ++ natToBits imm 8
      else
        return natToBits 0xaa 8 ++ natToBits imm 8
  | .rshiftConst quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let imm : Nat := bits - 1
      if quiet then
        return natToBits 0xb7ab 16 ++ natToBits imm 8
      else
        return natToBits 0xab 8 ++ natToBits imm 8
  | .lshift =>
      return natToBits 0xac 8
  | .rshift =>
      return natToBits 0xad 8
  | .equal =>
      return natToBits 0xba 8
  | .neq =>
      return natToBits 0xbd 8
  | .and_ =>
      return natToBits 0xb0 8
  | .or =>
      return natToBits 0xb1 8
  | .not_ =>
      return natToBits 0xb3 8
  | .sgn =>
      return natToBits 0xb8 8
  | .less =>
      return natToBits 0xb9 8
  | .leq =>
      return natToBits 0xbb 8
  | .greater =>
      return natToBits 0xbc 8
  | .geq =>
      return natToBits 0xbe 8
  | .cmp =>
      return natToBits 0xbf 8
  | .sbits =>
      return natToBits 0xd749 16
  | .srefs =>
      return natToBits 0xd74a 16
  | .sbitrefs =>
      return natToBits 0xd74b 16
  | .sempty =>
      return natToBits 0xc700 16
  | .sdempty =>
      return natToBits 0xc701 16
  | .srempty =>
      return natToBits 0xc702 16
  | .sdCntTrail0 =>
      return natToBits 0xc712 16
  | .sdEq =>
      return natToBits 0xc705 16
  | .sdcutfirst =>
      return natToBits 0xd720 16
  | .sdskipfirst =>
      return natToBits 0xd721 16
  | .sdcutlast =>
      return natToBits 0xd722 16
  | .sdskiplast =>
      return natToBits 0xd723 16
  | .sdBeginsX quiet =>
      return natToBits (if quiet then 0xd727 else 0xd726) 16
  | .sdBeginsConst .. =>
      throw .invOpcode
  | .lessInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc1 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .eqInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc0 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .gtInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc2 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .neqInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc3 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .pushNull =>
      return natToBits 0x6d 8
  | .isNull =>
      return natToBits 0x6e 8
  | .nullSwapIfNot =>
      return natToBits 0x6fa1 16
  | .mktuple n =>
      if n ≤ 15 then
        return natToBits (0x6f00 + n) 16
      else
        throw .rangeChk
  | .index idx =>
      if idx ≤ 15 then
        return natToBits (0x6f10 + idx) 16
      else
        throw .rangeChk
  | .untuple n =>
      if n ≤ 15 then
        return natToBits (0x6f20 + n) 16
      else
        throw .rangeChk
  | .tpush =>
      return natToBits 0x6f8c 16
  | .blkdrop2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        if args < 0x10 then
          throw .rangeChk
        return natToBits (0x6c00 + args) 16
      else
        throw .rangeChk
  | .pushSliceConst _ =>
      throw .invOpcode
  | .pushCont _ =>
      throw .invOpcode
  | .pushRefCont _ =>
      throw .invOpcode
  | .execute =>
      return natToBits 0xd8 8
  | .jmpx =>
      return natToBits 0xd9 8
  | .callxArgs params retVals =>
      if params > 15 then
        throw .rangeChk
      if retVals = -1 then
        return natToBits (0xdb00 + params) 16
      if decide (0 ≤ retVals ∧ retVals ≤ 15) then
        let args8 : Nat := (params <<< 4) + retVals.toNat
        return natToBits 0xda 8 ++ natToBits args8 8
      else
        throw .rangeChk
  | .jmpxArgs params =>
      if params > 15 then
        throw .rangeChk
      return natToBits (0xdb10 + params) 16
  | .ret =>
      return natToBits 0xdb30 16
  | .retAlt =>
      return natToBits 0xdb31 16
  | .retBool =>
      return natToBits 0xdb32 16
  | .retArgs n =>
      if n > 15 then
        throw .rangeChk
      return natToBits (0xdb20 + n) 16
  | .ifjmp =>
      return natToBits 0xe0 8
  | .ifnotjmp =>
      return natToBits 0xe1 8
  | .ifelse =>
      return natToBits 0xe2 8
  | .ifref _ =>
      throw .invOpcode
  | .ifnotref _ =>
      throw .invOpcode
  | .ifjmpref _ =>
      throw .invOpcode
  | .ifnotjmpref _ =>
      throw .invOpcode
  | .ifrefElse _ =>
      throw .invOpcode
  | .ifelseRef _ =>
      throw .invOpcode
  | .ifrefElseRef _ _ =>
      throw .invOpcode
  | .callRef _ =>
      throw .invOpcode
  | .callDict idx =>
      if idx < 256 then
        return natToBits (0xf000 + idx) 16
      else
        throw .rangeChk
  | .until =>
      return natToBits 0xe6 8
  | .while_ =>
      return natToBits 0xe8 8
  | .blkdrop n =>
      if n < 16 then
        return natToBits (0x5f00 + n) 16
      else
        throw .rangeChk
  | .drop2 =>
      return natToBits 0x5b 8
  | .balance =>
      return natToBits 0xf827 16
  | .now =>
      return natToBits 0xf823 16
  | .getParam idx =>
      if idx ≤ 15 then
        return natToBits (0xf820 + idx) 16
      else
        throw .rangeChk
  | .randu256 =>
      return natToBits 0xf810 16
  | .rand =>
      return natToBits 0xf811 16
  | .setRand mix =>
      return natToBits (if mix then 0xf815 else 0xf814) 16
  | .getGlobVar =>
      return natToBits 0xf840 16
  | .getGlob idx =>
      if idx = 0 ∨ idx > 31 then
        throw .rangeChk
      else
        return natToBits (0xf840 + idx) 16
  | .setGlobVar =>
      return natToBits 0xf860 16
  | .setGlob idx =>
      if idx = 0 ∨ idx > 31 then
        throw .rangeChk
      else
        return natToBits (0xf860 + idx) 16
  | .accept =>
      return natToBits 0xf800 16
  | .setGasLimit =>
      return natToBits 0xf801 16
  | .gasConsumed =>
      return natToBits 0xf807 16
  | .commit =>
      return natToBits 0xf80f 16
  | .ldGrams =>
      return natToBits 0xfa00 16
  | .stGrams =>
      return natToBits 0xfa02 16
  | .ldMsgAddr quiet =>
      return natToBits (if quiet then 0xfa41 else 0xfa40) 16
  | .rewriteStdAddr quiet =>
      return natToBits (if quiet then 0xfa45 else 0xfa44) 16
  | .hashCU =>
      return natToBits 0xf900 16
  | .hashSU =>
      return natToBits 0xf901 16
  | .chkSignU =>
      return natToBits 0xf910 16
  | .chkSignS =>
      return natToBits 0xf911 16
  | .sendMsg =>
      return natToBits 0xfb08 16
  | .sendRawMsg =>
      return natToBits 0xfb00 16
  | .rawReserve =>
      return natToBits 0xfb02 16
  | .throw exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf200 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2c0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwIf exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf240 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2d0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwIfNot exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf280 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2e0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwAny hasParam hasCond throwCond =>
      if !hasCond && throwCond then
        throw .rangeChk
      let args : Nat :=
        if !hasCond then
          if hasParam then 1 else 0
        else if throwCond then
          if hasParam then 3 else 2
        else
          if hasParam then 5 else 4
      return natToBits (0xf2f0 + args) 16
  | .try_ =>
      return natToBits 0xf2ff 16
  | .stdict =>
      return natToBits 0xf400 16
  | .skipdict =>
      return natToBits 0xf401 16
  | .lddict preload quiet =>
      let args : Nat := (if preload then 1 else 0) + (if quiet then 2 else 0)
      return natToBits (0xf404 + args) 16
  | .dictGet intKey unsigned byRef =>
      if intKey then
        let flags : Nat := (if byRef then 1 else 0) + (if unsigned then 2 else 0)
        return natToBits (0xf40c + flags) 16
      else
        if unsigned then throw .invOpcode
        return natToBits (if byRef then 0xf40b else 0xf40a) 16
  | .dictSet _ _ _ _ =>
      throw .invOpcode
  | .dictReplaceB intKey unsigned =>
      if intKey then
        return natToBits (if unsigned then 0xf44b else 0xf44a) 16
      else
        if unsigned then throw .invOpcode
        return natToBits 0xf449 16
  | .dictPushConst _ _ =>
      throw .invOpcode
  | .dictGetExec _ _ _ =>
      throw .invOpcode

def assembleCp0 (code : List Instr) : Except Excno Cell := do
  let mut bits : BitString := #[]
  for i in code do
    bits := bits ++ (← encodeCp0 i)
  return { bits, refs := #[] }

structure Regs where
  c0 : Continuation
  c1 : Continuation
  c2 : Continuation
  c3 : Continuation
  c4 : Cell
  c5 : Cell
  c7 : Array Value
  deriving Repr

def Regs.initial : Regs :=
  { c0 := .quit 0
    c1 := .quit 1
    c2 := .excQuit
    c3 := .quit 11
    c4 := Cell.empty
    c5 := Cell.empty
    c7 := #[] }

structure VmState where
  stack : Stack
  regs : Regs
  cc : Continuation
  cp : Int
  gas : GasLimits
  chksgnCounter : Nat
  loadedCells : Array (Array UInt8)
  callStack : Array CallFrame
  cstate : CommittedState
  maxDataDepth : Nat
  deriving Repr

def VmState.initial (code : Cell) (gasLimit : Int := 1_000_000) : VmState :=
  { stack := #[]
    regs := { Regs.initial with c3 := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty }
    cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty
    cp := 0
    gas := GasLimits.ofLimit gasLimit
    chksgnCounter := 0
    loadedCells := #[]
    callStack := #[]
    cstate := CommittedState.empty
    maxDataDepth := 512 }

abbrev VM := ExceptT Excno (StateM VmState)

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

def VM.popCell : VM Cell := do
  let v ← VM.pop
  match v with
  | .cell c => return c
  | _ => throw .typeChk

def VM.popSlice : VM Slice := do
  let v ← VM.pop
  match v with
  | .slice s => return s
  | _ => throw .typeChk

def VM.popBuilder : VM Builder := do
  let v ← VM.pop
  match v with
  | .builder b => return b
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
      VM.push (.int .nan)
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

def VM.popMaybeCell : VM (Option Cell) := do
  let v ← VM.pop
  match v with
  | .null => return none
  | .cell c => return some c
  | _ => throw .typeChk

def VmState.consumeGas (st : VmState) (amount : Int) : VmState :=
  { st with gas := st.gas.consume amount }

def VmState.registerChkSgnCall (st : VmState) : VmState :=
  let cnt := st.chksgnCounter + 1
  let st' := { st with chksgnCounter := cnt }
  if cnt > chksgnFreeCount then
    st'.consumeGas chksgnGasPrice
  else
    st'

def VmState.consumeTupleGas (st : VmState) (tupleLen : Nat) : VmState :=
  st.consumeGas (Int.ofNat tupleLen * tupleEntryGasPrice)

def VmState.consumeStackGas (st : VmState) (stackDepth : Nat) : VmState :=
  let extra : Nat := if stackDepth > freeStackDepth then stackDepth - freeStackDepth else 0
  st.consumeGas (Int.ofNat extra * stackEntryGasPrice)

def VmState.registerCellLoad (st : VmState) (c : Cell) : VmState :=
  let h : Array UInt8 := Cell.hashBytes c
  let seen : Bool := st.loadedCells.any (fun x => x == h)
  let st' : VmState :=
    if seen then
      st
    else
      { st with loadedCells := st.loadedCells.push h }
  st'.consumeGas (if seen then cellReloadGasPrice else cellLoadGasPrice)

def VmState.throwException (st : VmState) (exc : Int) : VmState :=
  let stack : Stack := #[.int (.num 0), .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.ret (st : VmState) : VmState :=
  let ret := st.regs.c0
  match ret with
  | .ordinary code saved cregs cdata =>
      { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
  | .quit n =>
      { st with regs := { st.regs with c0 := .quit 0 }, cc := .quit n }
  | .excQuit =>
      { st with regs := { st.regs with c0 := .quit 0 }, cc := .excQuit }
  | .whileCond cond body after =>
      { st with cc := .whileCond cond body after }
  | .whileBody cond body after =>
      { st with cc := .whileBody cond body after }
  | .untilBody body after =>
      { st with cc := .untilBody body after }

def VmState.retAlt (st : VmState) : VmState :=
  let old := st.regs.c1
  match old with
  | .ordinary code _ cregs cdata =>
      { st with regs := { st.regs with c1 := .quit 1 }, cc := .ordinary code (.quit 0) cregs cdata }
  | _ =>
      { st with regs := { st.regs with c1 := .quit 1 }, cc := old }

def VM.ret (passArgs : Int := -1) : VM Unit := do
  let st ← get
  if h : 0 < st.callStack.size then
    let frame := st.callStack.back (h := h)
    let expected : Int := frame.retArgs
    let copy : Int :=
      if decide (expected ≥ 0) then
        expected
      else if decide (passArgs ≥ 0) then
        passArgs
      else
        -1
    let vals : Stack ←
      if decide (copy < 0) then
        pure st.stack
      else
        let k : Nat := copy.toNat
        if k > st.stack.size then
          throw .stkUnd
        pure (st.stack.extract (st.stack.size - k) st.stack.size)
    let newStack : Stack := frame.savedStack ++ vals
    set { st with stack := newStack, callStack := st.callStack.pop }
  modify fun st => st.ret

def VmState.jumpTo (st : VmState) (k : Continuation) : VmState :=
  { st with cc := k }

def VmState.callTo (st : VmState) (k : Continuation) : VmState :=
  let oldC0 := st.regs.c0
  let retCont :=
    match st.cc with
    | .ordinary code _ _ _ => .ordinary code oldC0 OrdCregs.empty OrdCdata.empty
    | _ => .quit 0
  { st with regs := { st.regs with c0 := retCont }, cc := k }

def VmState.getCtr (st : VmState) (idx : Nat) : Except Excno Value :=
  match idx with
  | 0 => .ok (.cont st.regs.c0)
  | 1 => .ok (.cont st.regs.c1)
  | 2 => .ok (.cont st.regs.c2)
  | 3 => .ok (.cont st.regs.c3)
  | 4 => .ok (.cell st.regs.c4)
  | 5 => .ok (.cell st.regs.c5)
  | 7 => .ok (.tuple st.regs.c7)
  | _ => .error .rangeChk

def VmState.setCtr (st : VmState) (idx : Nat) (v : Value) : Except Excno VmState :=
  match idx, v with
  | 0, .cont k => .ok { st with regs := { st.regs with c0 := k } }
  | 1, .cont k => .ok { st with regs := { st.regs with c1 := k } }
  | 2, .cont k => .ok { st with regs := { st.regs with c2 := k } }
  | 3, .cont k => .ok { st with regs := { st.regs with c3 := k } }
  | 4, .cell c => .ok { st with regs := { st.regs with c4 := c } }
  | 5, .cell c => .ok { st with regs := { st.regs with c5 := c } }
  | 7, .tuple t => .ok { st with regs := { st.regs with c7 := t } }
  | 6, _ => .error .rangeChk
  | _, _ => .error .typeChk

def tupleExtendSetIndex (t : Array Value) (idx : Nat) (v : Value) : Array Value × Nat :=
  if idx < t.size then
    (t.set! idx v, t.size)
  else if v == .null then
    (t, 0)
  else
    let newSize := idx + 1
    let tExt := t ++ Array.replicate (newSize - t.size) Value.null
    (tExt.set! idx v, newSize)

def VM.generateRandu256 : VM Int := do
  -- Mirrors `generate_randu256` from `crypto/vm/tonops.cpp`:
  -- SHA512(seed) where seed is a 256-bit unsigned integer, then:
  --   new_seed := hash[0:32], rand := hash[32:64].
  let st ← get
  if 0 < st.regs.c7.size then
    match st.regs.c7[0]! with
    | .tuple params =>
        if 6 < params.size then
          match params[6]! with
          | .int (.num seed) =>
              if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                throw .rangeChk
              let seedBytes := natToBytesBEFixed seed.toNat 32
              let digest := sha512Digest seedBytes
              let newSeedNat := bytesToNatBE (digest.extract 0 32)
              let randNat := bytesToNatBE (digest.extract 32 64)
              let newSeed : Int := Int.ofNat newSeedNat
              let rand : Int := Int.ofNat randNat

              let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
              let outerSize := st.regs.c7.size
              let c7' := st.regs.c7.set! 0 (.tuple params')
              let mut st' := { st with regs := { st.regs with c7 := c7' } }
              if tpay > 0 then
                st' := st'.consumeTupleGas tpay
              st' := st'.consumeTupleGas outerSize
              set st'
              return rand
          | .int .nan =>
              throw .rangeChk
          | _ =>
              throw .typeChk
        else
          throw .typeChk
    | _ =>
        throw .typeChk
  else
    throw .typeChk

def execInstr (i : Instr) : VM Unit := do
  match i with
  | .nop =>
      pure ()
  | .pushInt n =>
      VM.pushIntQuiet n false
  | .pushPow2 exp =>
      VM.pushIntQuiet (.num (intPow2 exp)) false
  | .pushPow2Dec exp =>
      VM.pushIntQuiet (.num (intPow2 exp - 1)) false
  | .pushNegPow2 exp =>
      VM.pushIntQuiet (.num (-intPow2 exp)) false
  | .push idx =>
      let v ← VM.fetch idx
      VM.push v
  | .pop idx =>
      -- Mirror the C++ behavior: swap top with s[idx], then pop the top.
      VM.swap 0 idx
      let _ ← VM.pop
      pure ()
  | .xchg0 idx =>
      VM.swap 0 idx
  | .xchg1 idx =>
      VM.swap 1 idx
  | .xchg x y =>
      if decide (x = 0 ∨ y ≤ x) then
        throw .invOpcode
      let st ← get
      if y < st.stack.size then
        VM.swap x y
      else
        throw .stkUnd
  | .xchg2 x y =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
      else
        throw .stkUnd
  | .xchg3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 2
      if need < st.stack.size then
        VM.swap 2 x
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | .xcpu x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        VM.swap 0 x
        let v ← VM.fetch y
        VM.push v
      else
        throw .stkUnd
  | .xc2pu x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max (Nat.max x y) z) 1
      if need < st.stack.size then
        VM.swap 1 x
        VM.swap 0 y
        let v ← VM.fetch z
        VM.push v
      else
        throw .stkUnd
  | .xcpuxc x y z =>
      let st ← get
      if decide (st.stack.size > Nat.max (Nat.max x y) 1 ∧ z ≤ st.stack.size) then
        VM.swap 1 x
        let v ← VM.fetch y
        VM.push v
        VM.swap 0 1
        VM.swap 0 z
      else
        throw .stkUnd
  | .xcpu2 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        VM.swap 0 x
        let v1 ← VM.fetch y
        VM.push v1
        let v2 ← VM.fetch (z + 1)
        VM.push v2
      else
        throw .stkUnd
  | .puxc2 x y z =>
      let st ← get
      if x < st.stack.size && 1 < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 2
        VM.swap 1 y
        VM.swap 0 z
      else
        throw .stkUnd
  | .puxc x y =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
      else
        throw .stkUnd
  | .puxcpu x y z =>
      let st ← get
      if x < st.stack.size && y ≤ st.stack.size && z ≤ st.stack.size then
        let v ← VM.fetch x
        VM.push v
        VM.swap 0 1
        VM.swap 0 y
        let v2 ← VM.fetch z
        VM.push v2
      else
        throw .stkUnd
  | .push2 x y =>
      let st ← get
      let need : Nat := Nat.max x y
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
      else
        throw .stkUnd
  | .push3 x y z =>
      let st ← get
      let need : Nat := Nat.max (Nat.max x y) z
      if need < st.stack.size then
        let v1 ← VM.fetch x
        VM.push v1
        let v2 ← VM.fetch (y + 1)
        VM.push v2
        let v3 ← VM.fetch (z + 2)
        VM.push v3
      else
        throw .stkUnd
  | .blkSwap x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let front := st.stack.take (n - total)
        let below := st.stack.extract (n - total) (n - y)
        let top := st.stack.extract (n - y) n
        modify fun st => { st with stack := front ++ top ++ below }
      else
        throw .stkUnd
  | .rot =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 1 2
        VM.swap 0 1
      else
        throw .stkUnd
  | .rotRev =>
      let st ← get
      if 2 < st.stack.size then
        VM.swap 0 1
        VM.swap 1 2
      else
        throw .stkUnd
  | .twoSwap =>
      let st ← get
      if 3 < st.stack.size then
        VM.swap 1 3
        VM.swap 0 2
      else
        throw .stkUnd
  | .twoOver =>
      let v1 ← VM.fetch 3
      VM.push v1
      let v2 ← VM.fetch 3
      VM.push v2
  | .reverse x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let start : Nat := n - total
        let stop : Nat := n - y
        let arr := Id.run do
          let mut a := st.stack
          for i in [0:(x / 2)] do
            let i1 : Nat := start + i
            let i2 : Nat := stop - 1 - i
            let v1 := a[i1]!
            let v2 := a[i2]!
            a := a.set! i1 v2
            a := a.set! i2 v1
          return a
        set { st with stack := arr }
      else
        throw .stkUnd
  | .tuck =>
      VM.swap 0 1
      let v ← VM.fetch 1
      VM.push v
  | .pushCtr idx =>
      let st ← get
      match st.getCtr idx with
      | .ok v => VM.push v
      | .error e => throw e
  | .popCtr idx =>
      let v ← VM.pop
      let st ← get
      match st.setCtr idx v with
      | .ok st' => set st'
      | .error e => throw e
  | .setContCtr idx =>
      let cont ← VM.popCont
      let v ← VM.pop
      match cont, idx, v with
      | .ordinary code saved cregs cdata, 4, .cell c =>
          match cregs.c4 with
          | none => VM.push (.cont (.ordinary code saved { cregs with c4 := some c } cdata))
          | some _ => throw .typeChk
      | .ordinary code saved cregs cdata, 5, .cell c =>
          match cregs.c5 with
          | none => VM.push (.cont (.ordinary code saved { cregs with c5 := some c } cdata))
          | some _ => throw .typeChk
      | .ordinary code saved cregs cdata, 7, .tuple t =>
          -- `define_c7` in C++ never fails; it just keeps the existing one if present.
          let cregs' : OrdCregs :=
            match cregs.c7 with
            | some _ => cregs
            | none => { cregs with c7 := some t }
          VM.push (.cont (.ordinary code saved cregs' cdata))
      | .ordinary _ _ _ _, 4, _ => throw .typeChk
      | .ordinary _ _ _ _, 5, _ => throw .typeChk
      | .ordinary _ _ _ _, 7, _ => throw .typeChk
      | _, _, _ =>
          throw .typeChk
  | .setContVarArgs =>
      -- Mirrors `SETCONTVARARGS` from `crypto/vm/contops.cpp` (exec_setcont_varargs + exec_setcontargs_common).
      -- Stack effect: ... <args...> cont copy more -- ... cont
      let more ← VM.popIntFinite
      if decide (more < -1 ∨ more > 255) then
        throw .rangeChk
      let copy ← VM.popIntFinite
      if decide (copy < 0 ∨ copy > 255) then
        throw .rangeChk
      let copyN : Nat := copy.toNat
      let st ← get
      if copyN + 1 > st.stack.size then
        throw .stkUnd
      let cont ← VM.popCont
      match cont with
      | .ordinary code saved cregs cdata =>
          let mut cdata := cdata
          if copyN > 0 then
            if decide (0 ≤ cdata.nargs ∧ cdata.nargs < copy) then
              throw .stkOv
            let st0 ← get
            let depth : Nat := st0.stack.size
            let start : Nat := depth - copyN
            let captured : Array Value := st0.stack.extract start depth
            let remaining : Stack := st0.stack.take start
            set { st0 with stack := remaining }
            cdata := { cdata with stack := cdata.stack ++ captured }
            if decide (0 ≤ cdata.nargs) then
              cdata := { cdata with nargs := cdata.nargs - copy }
          if decide (more ≥ 0) then
            if decide (cdata.nargs > more) then
              cdata := { cdata with nargs := 0x40000000 }
            else if decide (cdata.nargs < 0) then
              cdata := { cdata with nargs := more }
          VM.push (.cont (.ordinary code saved cregs cdata))
      | _ =>
          throw .typeChk
  | .saveCtr _idx =>
      -- NOTE: stubbed for now (we don't model saved control registers inside continuations yet).
      pure ()
  | .sameAlt =>
      modify fun st => { st with regs := { st.regs with c1 := st.regs.c0 } }
  | .sameAltSave =>
      -- NOTE: the “save” part is stubbed (no saved control regs in continuations yet).
      modify fun st => { st with regs := { st.regs with c1 := st.regs.c0 } }
  | .boolAnd =>
      let val ← VM.popCont
      let cont ← VM.popCont
      match cont with
      | .ordinary code saved cregs cdata =>
          let cregs' : OrdCregs :=
            match cregs.c0 with
            | some _ => cregs
            | none => { cregs with c0 := some val }
          VM.push (.cont (.ordinary code saved cregs' cdata))
      | _ =>
          throw .typeChk
  | .boolOr =>
      let val ← VM.popCont
      let cont ← VM.popCont
      match cont with
      | .ordinary code saved cregs cdata =>
          let cregs' : OrdCregs :=
            match cregs.c1 with
            | some _ => cregs
            | none => { cregs with c1 := some val }
          VM.push (.cont (.ordinary code saved cregs' cdata))
      | _ =>
          throw .typeChk
  | .composBoth =>
      let val ← VM.popCont
      let cont ← VM.popCont
      match cont with
      | .ordinary code saved cregs cdata =>
          let cregs0 : OrdCregs :=
            match cregs.c0 with
            | some _ => cregs
            | none => { cregs with c0 := some val }
          let cregs1 : OrdCregs :=
            match cregs0.c1 with
            | some _ => cregs0
            | none => { cregs0 with c1 := some val }
          VM.push (.cont (.ordinary code saved cregs1 cdata))
      | _ =>
          throw .typeChk
  | .ctos =>
      let c ← VM.popCell
      -- C++ `CTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
  | .xctos =>
      let c ← VM.popCell
      -- C++ `XCTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
      -- C++ `XCTOS` also returns a boolean `is_special`. We don't model special cells yet,
      -- and our current BOC fast-path rejects exotic cells, so return `false` (0).
      VM.pushSmallInt 0
  | .newc =>
      VM.push (.builder Builder.empty)
  | .endc =>
      let b ← VM.popBuilder
      VM.push (.cell b.finalize)
  | .ends =>
      let s ← VM.popSlice
      if s.bitsRemaining == 0 && s.refsRemaining == 0 then
        pure ()
      else
        throw .cellUnd
  | .sbits =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
  | .srefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | .sbitrefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | .sempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 && s.refsRemaining == 0 then -1 else 0)
  | .sdempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 then -1 else 0)
  | .srempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.refsRemaining == 0 then -1 else 0)
  | .sdCntTrail0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let endPos : Nat := s.cell.bits.size
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[endPos - 1 - cnt]! == false do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | .sdEq =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      let c1 := s1.toCellRemaining
      let c2 := s2.toCellRemaining
      VM.pushSmallInt (if c1 == c2 then -1 else 0)
  | .sdcutfirst =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let newCell : Cell :=
          { bits := s.cell.bits.extract s.bitPos (s.bitPos + bits)
            refs := s.cell.refs.extract s.refPos s.cell.refs.size }
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sdskipfirst =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | .sdcutlast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let drop : Nat := s.bitsRemaining - bits
        VM.push (.slice (s.advanceBits drop))
      else
        throw .cellUnd
  | .sdskiplast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let keep : Nat := s.bitsRemaining - bits
        let newCell : Cell :=
          { bits := s.cell.bits.extract s.bitPos (s.bitPos + keep)
            refs := s.cell.refs.extract s.refPos s.cell.refs.size }
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sdBeginsX quiet =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        VM.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .sdBeginsConst quiet pref =>
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        VM.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .ldu bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n := bitsToNat bs
        VM.push (.int (.num (Int.ofNat n)))
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | .loadInt unsigned prefetch quiet bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n : Int :=
          if unsigned then
            Int.ofNat (bitsToNat bs)
          else
            bitsToIntSignedTwos bs
        VM.pushIntQuiet (.num n) false
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
          else
            throw .cellUnd
  | .loadIntVar unsigned prefetch quiet =>
      -- Stack effect: ... slice bits -- ...
      -- Bits may be 0..257 for signed, 0..256 for unsigned (per C++ pop_smallint_range).
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n : Int :=
          if unsigned then
            Int.ofNat (bitsToNat bs)
          else
            bitsToIntSignedTwos bs
        VM.pushIntQuiet (.num n) false
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .ldref =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        VM.push (.cell c)
        VM.push (.slice { s with refPos := s.refPos + 1 })
      else
        throw .cellUnd
  | .pldRefIdx idx =>
      let s ← VM.popSlice
      if s.haveRefs (idx + 1) then
        let pos := s.refPos + idx
        if pos < s.cell.refs.size then
          let c := s.cell.refs[pos]!
          VM.push (.cell c)
        else
          throw .cellUnd
      else
        throw .cellUnd
  | .loadSliceX prefetch quiet =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let subBits := s.readBits bits
        let subCell : Cell := { bits := subBits, refs := #[] }
        VM.push (.slice (Slice.ofCell subCell))
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .loadSliceFixed prefetch quiet bits =>
      let s ← VM.popSlice
      if s.haveBits bits then
        let subBits := s.readBits bits
        let subCell : Cell := { bits := subBits, refs := #[] }
        VM.push (.slice (Slice.ofCell subCell))
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .sti bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STI`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          match intToBitsTwos n bits with
          | .ok bs => VM.push (.builder (b.storeBits bs))
          | .error e => throw e
  | .stu bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STU`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if decide (n < 0 ∨ n ≥ intPow2 bits) then
            throw .rangeChk
          let bs := natToBits n.toNat bits
          VM.push (.builder (b.storeBits bs))
  | .stIntVar unsigned rev quiet =>
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
      let (x, b) ←
        if rev then
          let x ← VM.popInt
          let b ← VM.popBuilder
          pure (x, b)
        else
          let b ← VM.popBuilder
          let x ← VM.popInt
          pure (x, b)

      if !b.canExtendBy bits then
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.int x)
          else
            VM.push (.int x)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
      else
        let fits : Bool :=
          match x with
          | .nan => false
          | .num n =>
              if bits = 0 then
                n = 0
              else if unsigned then
                decide (0 ≤ n ∧ n < intPow2 bits)
              else
                intSignedFitsBits n bits
        if !fits then
          if quiet then
            if rev then
              VM.push (.builder b)
              VM.push (.int x)
            else
              VM.push (.int x)
              VM.push (.builder b)
            VM.pushSmallInt 1
          else
            throw .rangeChk
        else
          match x with
          | .nan =>
              -- unreachable due to `fits` check
              throw .rangeChk
          | .num n =>
              let bs : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .ok bs => pure bs
                  | .error e => throw e
              VM.push (.builder (b.storeBits bs))
              if quiet then
                VM.pushSmallInt 0
  | .stIntFixed unsigned rev quiet bits =>
      let (x, b) ←
        if rev then
          let x ← VM.popInt
          let b ← VM.popBuilder
          pure (x, b)
        else
          let b ← VM.popBuilder
          let x ← VM.popInt
          pure (x, b)

      if !b.canExtendBy bits then
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.int x)
          else
            VM.push (.int x)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
      else
        let fits : Bool :=
          match x with
          | .nan => false
          | .num n =>
              if bits = 0 then
                n = 0
              else if unsigned then
                decide (0 ≤ n ∧ n < intPow2 bits)
              else
                intSignedFitsBits n bits
        if !fits then
          if quiet then
            if rev then
              VM.push (.builder b)
              VM.push (.int x)
            else
              VM.push (.int x)
              VM.push (.builder b)
            VM.pushSmallInt 1
          else
            throw .rangeChk
        else
          match x with
          | .nan =>
              -- unreachable due to `fits` check
              throw .rangeChk
          | .num n =>
              let bs : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .ok bs => pure bs
                  | .error e => throw e
              VM.push (.builder (b.storeBits bs))
              if quiet then
                VM.pushSmallInt 0
  | .stSlice rev quiet =>
      if rev then
        -- Stack: ... builder slice -- ...
        let s ← VM.popSlice
        let b ← VM.popBuilder
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.slice s)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... slice builder -- ...
        let b ← VM.popBuilder
        let s ← VM.popSlice
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.slice s)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | .stref =>
      -- Stack: ... cell builder -- ...  (builder on top)
      let b ← VM.popBuilder
      let c ← VM.popCell
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
      else
        throw .cellOv
  | .bbits =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat b.bits.size)
  | .stSliceConst sConst =>
      let b ← VM.popBuilder
      let c := sConst.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
        VM.push (.builder b')
      else
        throw .cellOv
  | .stZeroes =>
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits false)))
      else
        throw .cellOv
  | .stOnes =>
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits true)))
      else
        throw .cellOv
  | .stSame =>
      let vNat ← VM.popNatUpTo 1
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits (vNat == 1))))
      else
        throw .cellOv
  | .setcp cp =>
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        throw .invOpcode
  | .ifret =>
      if (← VM.popBool) then
        VM.ret
      else
        pure ()
  | .ifnotret =>
      if !(← VM.popBool) then
        VM.ret
      else
        pure ()
  | .if_ =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont
      else
        pure ()
  | .ifnot =>
      let cont ← VM.popCont
      if !(← VM.popBool) then
        modify fun st => st.callTo cont
      else
        pure ()
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
  | .nullSwapIfNot =>
      let x ← VM.popIntFinite
      if x == 0 then
        VM.push .null
      VM.push (.int (.num x))
  | .mktuple n =>
      let st ← get
      if n ≤ st.stack.size then
        let mut items : Array Value := #[]
        for _ in [0:n] do
          items := items.push (← VM.pop)
        VM.push (.tuple items.reverse)
        modify fun st => st.consumeTupleGas n
      else
        throw .stkUnd
  | .index idx =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if idx < items.size then
            VM.push (items[idx]!)
          else
            VM.push .null
      | _ =>
          throw .typeChk
  | .untuple n =>
      let v ← VM.pop
      match v with
      | .tuple items =>
          if items.size = n then
            for i in [0:n] do
              VM.push (items[i]!)
            modify fun st => st.consumeTupleGas n
          else
            throw .typeChk
      | _ =>
          throw .typeChk
  | .tpush =>
      let x ← VM.pop
      let t ← VM.pop
      match t with
      | .tuple items =>
          if items.size > 254 then
            throw .rangeChk
          let out := items.push x
          VM.push (.tuple out)
          modify fun st => st.consumeTupleGas out.size
      | _ =>
          throw .typeChk
  | .pushSliceConst s =>
      VM.push (.slice s)
  | .pushCont code =>
      VM.push (.cont (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty))
  | .pushRefCont c =>
      modify fun st => st.registerCellLoad c
      VM.push (.cont (.ordinary (Slice.ofCell c) (.quit 0) OrdCregs.empty OrdCdata.empty))
  | .execute =>
      let cont ← VM.popCont
      modify fun st => st.callTo cont
  | .jmpx =>
      let cont ← VM.popCont
      modify fun st => st.jumpTo cont
  | .callxArgs params retVals =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let split : Nat := depth - params
      let saved : Stack := st.stack.take split
      let args : Stack := st.stack.extract split depth
      let frame : CallFrame := { savedStack := saved, retArgs := retVals }
      set { st with stack := args, callStack := st.callStack.push frame }
      modify fun st => st.callTo cont
  | .jmpxArgs params =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let start : Nat := depth - params
      let args : Stack := st.stack.extract start depth
      set { st with stack := args }
      modify fun st => st.jumpTo cont
  | .ret =>
      VM.ret
  | .retAlt =>
      modify fun st => st.retAlt
  | .retBool =>
      if (← VM.popBool) then
        VM.ret
      else
        modify fun st => st.retAlt
  | .retArgs n =>
      VM.ret (Int.ofNat n)
  | .ifjmp =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.jumpTo cont
      else
        pure ()
  | .ifnotjmp =>
      let cont ← VM.popCont
      if !(← VM.popBool) then
        modify fun st => st.jumpTo cont
      else
        pure ()
  | .ifelse =>
      let cont0 ← VM.popCont
      let cont1 ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont1
      else
        modify fun st => st.callTo cont0
  | .ifref code =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifnotref code =>
      if !(← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifjmpref code =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.jumpTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifnotjmpref code =>
      if !(← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.jumpTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        pure ()
  | .ifrefElse code =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        modify fun st => st.callTo cont
  | .ifelseRef code =>
      let cont ← VM.popCont
      if (← VM.popBool) then
        modify fun st => st.callTo cont
      else
        modify fun st => st.registerCellLoad code.cell
        modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .ifrefElseRef t f =>
      if (← VM.popBool) then
        modify fun st => st.registerCellLoad t.cell
        modify fun st => st.callTo (.ordinary t (.quit 0) OrdCregs.empty OrdCdata.empty)
      else
        modify fun st => st.registerCellLoad f.cell
        modify fun st => st.callTo (.ordinary f (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .callRef code =>
      modify fun st => st.registerCellLoad code.cell
      modify fun st => st.callTo (.ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty)
  | .callDict idx =>
      VM.pushSmallInt (Int.ofNat idx)
      modify fun st => st.callTo st.regs.c3
  | .until =>
      -- Stack effect: ... body -- ...
      -- Control flow: execute `body`; if it returns `true` then continue, otherwise repeat.
      let body ← VM.popCont
      let st ← get
      let after :=
        match st.cc with
        | .ordinary rest _ _ _ => .ordinary rest st.regs.c0 OrdCregs.empty OrdCdata.empty
        | _ => st.cc
      set { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
  | .while_ =>
      -- Stack effect: ... cond body -- ...
      -- Control flow: execute `cond`; if true then execute `body` and repeat.
      let body ← VM.popCont
      let cond ← VM.popCont
      let st ← get
      -- Capture the "after" continuation as the rest of the current code,
      -- but remember the current return continuation in `savedC0` so we can restore it when the loop terminates.
      let after :=
        match st.cc with
        | .ordinary rest _ _ _ => .ordinary rest st.regs.c0 OrdCregs.empty OrdCdata.empty
        | _ => st.cc
      set { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | .blkdrop2 x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let keepBottom : Nat := st.stack.size - total
        let bottom := st.stack.take keepBottom
        let top := st.stack.extract (keepBottom + x) st.stack.size
        modify fun st => { st with stack := bottom ++ top }
      else
        throw .stkUnd
  | .blkdrop n =>
      let st ← get
      if n ≤ st.stack.size then
        let keep : Nat := st.stack.size - n
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | .drop2 =>
      let st ← get
      if 2 ≤ st.stack.size then
        let keep : Nat := st.stack.size - 2
        modify fun st => { st with stack := st.stack.take keep }
      else
        throw .stkUnd
  | .balance =>
      -- BALANCE is `GETPARAM 7` in the TON opcode table; it reads `c7[0]` as the "params" tuple.
      let st ← get
      if h : 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 7 < params.size then
              VM.push (params[7]!)
            else
              VM.push .null
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | .now =>
      -- NOW is `GETPARAM 3` in the TON opcode table; it reads `c7[0]` as the "params" tuple.
      let st ← get
      if h : 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 3 < params.size then
              VM.push (params[3]!)
            else
              VM.push .null
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | .getParam idx =>
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if idx < params.size then
              VM.push (params[idx]!)
            else
              VM.push .null
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | .randu256 =>
      let y ← VM.generateRandu256
      VM.pushIntQuiet (.num y) false
  | .rand =>
      let x ← VM.popIntFinite
      let y ← VM.generateRandu256
      let z := floorDivPow2 (x * y) 256
      VM.pushIntQuiet (.num z) false
  | .setRand mix =>
      let x ← VM.popIntFinite
      if decide (x < 0 ∨ x ≥ intPow2 256) then
        throw .rangeChk
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            let newSeed : Int ←
              if mix then
                if 6 < params.size then
                  match params[6]! with
                  | .int (.num seed) =>
                      if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                        throw .rangeChk
                      let seedBytes := natToBytesBEFixed seed.toNat 32
                      let xBytes := natToBytesBEFixed x.toNat 32
                      let digest := sha256Digest (seedBytes ++ xBytes)
                      pure (Int.ofNat (bytesToNatBE digest))
                  | .int .nan => throw .rangeChk
                  | _ => throw .typeChk
                else
                  throw .rangeChk
              else
                pure x

            let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
            let outerSize := st.regs.c7.size
            let c7' := st.regs.c7.set! 0 (.tuple params')
            let mut st' := { st with regs := { st.regs with c7 := c7' } }
            if tpay > 0 then
              st' := st'.consumeTupleGas tpay
            st' := st'.consumeTupleGas outerSize
            set st'
        | _ =>
            throw .typeChk
      else
        throw .typeChk
  | .getGlobVar =>
      let idx ← VM.popNatUpTo 254
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | .getGlob idx =>
      let st ← get
      if idx < st.regs.c7.size then
        VM.push (st.regs.c7[idx]!)
      else
        VM.push .null
  | .setGlobVar =>
      let idx ← VM.popNatUpTo 254
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | .setGlob idx =>
      let x ← VM.pop
      let st ← get
      let (t', pay) := tupleExtendSetIndex st.regs.c7 idx x
      let mut st' := { st with regs := { st.regs with c7 := t' } }
      if pay > 0 then
        st' := st'.consumeTupleGas pay
      set st'
  | .accept =>
      let st ← get
      -- C++: change gas limit to GasLimits::infty.
      let st' := { st with gas := st.gas.changeLimit GasLimits.infty }
      set st'
  | .setGasLimit =>
      let n ← VM.popIntFinite
      let gas63 : Int := Int.ofNat (1 <<< (63 : Nat))
      let newLimit : Int :=
        if n > 0 then
          if n < gas63 then n else GasLimits.infty
        else
          0
      let st ← get
      if newLimit < st.gas.gasConsumed then
        throw .outOfGas
      set { st with gas := st.gas.changeLimit newLimit }
  | .gasConsumed =>
      let st ← get
      VM.pushSmallInt st.gas.gasConsumed
  | .commit =>
      let st ← get
      if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
        set { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } }
      else
        throw .cellOv
  | .ldGrams =>
      let csr0 ← VM.popSlice
      let (len, csr1) ← csr0.takeBitsAsNatCellUnd 4
      let dataBits : Nat := len * 8
      if csr1.haveBits dataBits then
        let bs := csr1.readBits dataBits
        let n : Nat := bitsToNat bs
        VM.pushIntQuiet (.num (Int.ofNat n)) false
        VM.push (.slice (csr1.advanceBits dataBits))
      else
        throw .cellUnd
  | .stGrams =>
      -- Mirrors `util::store_var_integer` (len_bits=4, unsigned) used by `STGRAMS`.
      -- Stack: ... builder x -- ...
      let x ← VM.popInt
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if n < 0 then
            throw .rangeChk
          let b ← VM.popBuilder
          let bitsLen : Nat := natLenBits n.toNat
          let lenBytes : Nat := (bitsLen + 7) / 8
          if lenBytes ≥ 16 then
            throw .rangeChk
          let totalBits : Nat := 4 + lenBytes * 8
          if !b.canExtendBy totalBits then
            throw .cellOv
          let bs := natToBits lenBytes 4 ++ natToBits n.toNat (lenBytes * 8)
          VM.push (.builder (b.storeBits bs))
  | .ldMsgAddr quiet =>
      let csr0 ← VM.popSlice
      match csr0.skipMessageAddr with
      | .ok csr1 =>
          let addrCell := Slice.prefixCell csr0 csr1
          VM.push (.slice (Slice.ofCell addrCell))
          VM.push (.slice csr1)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.push (.slice csr0)
            VM.pushSmallInt 0
          else
            throw e
  | .rewriteStdAddr quiet =>
      let csr0 ← VM.popSlice
      let parsed : Except Excno (Int × Nat) := do
        let (tag, s2) ← csr0.takeBitsAsNatCellUnd 2
        if tag != 2 then
          throw .cellUnd
        let s3 ← s2.skipMaybeAnycast
        let (wcNat, sWc) ← s3.takeBitsAsNatCellUnd 8
        if !sWc.haveBits 256 then
          throw .cellUnd
        let addrBits := sWc.readBits 256
        let sEnd := sWc.advanceBits 256
        if sEnd.bitsRemaining != 0 || sEnd.refsRemaining != 0 then
          throw .cellUnd
        let wc : Int := natToIntSignedTwos wcNat 8
        let addr : Nat := bitsToNat addrBits
        return (wc, addr)
      match parsed with
      | .ok (wc, addr) =>
          VM.pushSmallInt wc
          VM.pushIntQuiet (.num (Int.ofNat addr)) false
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw e
  | .hashCU =>
      let c ← VM.popCell
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | .hashSU =>
      let s ← VM.popSlice
      -- C++ `HASHSU` builds a temporary cell from the slice and hashes it; `CellBuilder::finalize()`
      -- charges `cell_create_gas_price`.
      modify fun st => st.consumeGas cellCreateGasPrice
      let c := s.toCellRemaining
      let h := Cell.hashBytes c
      let n := bytesToNatBE h
      VM.pushIntQuiet (.num (Int.ofNat n)) false
  | .chkSignU =>
      let key ← VM.popInt
      let sigSlice ← VM.popSlice
      let hash ← VM.popInt

      let msgBytes ←
        match exportUInt256BE hash with
        | .ok bs => pure bs
        | .error e => throw e
      let sigBytes ←
        match sigSlice.prefetchBytesCellUnd 64 with
        | .ok bs => pure bs
        | .error e => throw e
      let keyBytes ←
        match exportUInt256BE key with
        | .ok bs => pure bs
        | .error e => throw e

      modify fun st => st.registerChkSgnCall
      let ok := ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | .chkSignS =>
      let key ← VM.popInt
      let sigSlice ← VM.popSlice
      let dataSlice ← VM.popSlice
      if dataSlice.bitsRemaining % 8 ≠ 0 then
        throw .cellUnd
      let dataLen : Nat := dataSlice.bitsRemaining / 8
      if dataLen > 128 then
        throw .rangeChk

      let msgBytes ←
        match dataSlice.prefetchBytesCellUnd dataLen with
        | .ok bs => pure bs
        | .error e => throw e
      let sigBytes ←
        match sigSlice.prefetchBytesCellUnd 64 with
        | .ok bs => pure bs
        | .error e => throw e
      let keyBytes ←
        match exportUInt256BE key with
        | .ok bs => pure bs
        | .error e => throw e

      modify fun st => st.registerChkSgnCall
      let ok := ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | .sendMsg =>
      -- Partial `SENDMSG` implementation:
      -- - We still don't compute fees or fully validate TL-B message structure.
      -- - We *do* approximate the VM gas side-effects by loading the message cell (and its reachable subcells),
      --   similarly to how the C++ implementation unpacks the message and computes storage stats.
      let modeNat ← VM.popNatUpTo 2047
      let send : Bool := (modeNat &&& 1024) = 0
      let mode8 : Nat := modeNat &&& 0x3ff
      if mode8 ≥ 256 then
        throw .rangeChk
      let msgCell ← VM.popCell

      -- C++ `SENDMSG` loads the message cell (and then loads it again while traversing the message to compute
      -- forwarding fees / storage stats). We approximate this by:
      -- - one load of the root cell (unpack)
      -- - one reload of the root cell (stats)
      -- - one load of each reachable subcell (stats traversal with a visited set)
      modify fun st => st.registerCellLoad msgCell
      modify fun st => st.registerCellLoad msgCell
      let mut todo : Array Cell := msgCell.refs
      let mut seen : Array (Array UInt8) := #[]
      while todo.size > 0 do
        let c := todo.get! (todo.size - 1)
        todo := todo.pop
        let h := Cell.hashBytes c
        if !(seen.any (fun x => x == h)) then
          seen := seen.push h
          modify fun st => st.registerCellLoad c
          todo := todo ++ c.refs

      -- fees (fwd_fee + ihr_fee) placeholder
      VM.pushSmallInt 0
      if send then
        modify fun st => st.consumeGas cellCreateGasPrice
        let st ← get
        let prev := st.regs.c5
        let bits := natToBits 0x0ec3c86d 32 ++ natToBits mode8 8
        let newHead : Cell := { bits, refs := #[prev, msgCell] }
        set { st with regs := { st.regs with c5 := newHead } }
      else
        pure ()
  | .sendRawMsg =>
      let mode ← VM.popNatUpTo 255
      let msgCell ← VM.popCell
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let bits := natToBits 0x0ec3c86d 32 ++ natToBits mode 8
      let newHead : Cell := { bits, refs := #[prev, msgCell] }
      set { st with regs := { st.regs with c5 := newHead } }
  | .rawReserve =>
      let f ← VM.popNatUpTo 31
      let x ← VM.popIntFinite
      if x < 0 then
        throw .rangeChk
      let bitsLen : Nat := natLenBits x.toNat
      let lenBytes : Nat := (bitsLen + 7) / 8
      if lenBytes ≥ 16 then
        throw .rangeChk
      let gramsBits : BitString := natToBits lenBytes 4 ++ natToBits x.toNat (lenBytes * 8)
      let bits : BitString := natToBits 0x36e6b809 32 ++ natToBits f 8 ++ gramsBits ++ #[false]
      if bits.size > 1023 then
        throw .cellOv
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let newHead : Cell := { bits, refs := #[prev] }
      set { st with regs := { st.regs with c5 := newHead } }
  | .throw exc =>
      modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
  | .throwIf exc =>
      if (← VM.popBool) then
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
      else
        pure ()
  | .throwIfNot exc =>
      let flag ← VM.popBool
      if flag then
        pure ()
      else
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
  | .throwAny hasParam hasCond throwCond =>
      let flag ←
        if hasCond then
          VM.popBool
        else
          pure throwCond
      let excnoNat ← VM.popNatUpTo 0xffff
      let excno : Int := Int.ofNat excnoNat
      if flag != throwCond then
        if hasParam then
          let _ ← VM.pop
          pure ()
        else
          pure ()
      else
        if hasParam then
          let _ ← VM.pop
          modify fun st => (st.throwException excno).consumeGas exceptionGasPrice
        else
          modify fun st => (st.throwException excno).consumeGas exceptionGasPrice
  | .try_ =>
      let handler ← VM.popCont
      let cont ← VM.popCont
      let st ← get
      let codeAfter : Slice ←
        match st.cc with
        | .ordinary code _ _ _ => pure code
        | _ => throw .typeChk
      let cc : Continuation := .ordinary codeAfter st.regs.c0 OrdCregs.empty OrdCdata.empty
      let oldC2 : Continuation := st.regs.c2
      let handler' : Continuation ←
        match handler with
        | .ordinary hCode hSaved hCregs hCdata =>
            let hCregs0 : OrdCregs :=
              match hCregs.c2 with
              | some _ => hCregs
              | none => { hCregs with c2 := some oldC2 }
            let hCregs1 : OrdCregs :=
              match hCregs0.c0 with
              | some _ => hCregs0
              | none => { hCregs0 with c0 := some cc }
            pure (.ordinary hCode hSaved hCregs1 hCdata)
        | _ =>
            throw .typeChk
      set { st with regs := { st.regs with c0 := cc, c2 := handler' }, cc := cont }
  | .stdict =>
      -- Builder is on top, dict root cell (or null) below.
      let b ← VM.popBuilder
      let d? ← VM.popMaybeCell
      let hasRef : Bool := d?.isSome
      let needRefs : Nat := if hasRef then 1 else 0
      if !b.canExtendBy 1 needRefs then
        throw .cellOv
      let b1 := b.storeBits #[hasRef]
      let b2 :=
        match d? with
        | some c => { b1 with refs := b1.refs.push c }
        | none => b1
      VM.push (.builder b2)
  | .skipdict =>
      let s ← VM.popSlice
      if !s.haveBits 1 then
        throw .cellUnd
      let present : Bool := (s.readBits 1)[0]!
      let needRefs : Nat := if present then 1 else 0
      if !s.haveRefs needRefs then
        throw .cellUnd
      VM.push (.slice { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs })
  | .dictPushConst dict keyBits =>
      VM.push (.cell dict)
      VM.pushSmallInt (Int.ofNat keyBits)
  | .dictGet intKey unsigned byRef =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits? : Option BitString ←
        if intKey then
          let idx ← VM.popIntFinite
          pure (dictKeyBits? idx n unsigned)
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (some (keySlice.readBits n))
          else
            throw .cellUnd
      match keyBits? with
      | none =>
          -- Dictionary index out of bounds: behave like "not found".
          VM.pushSmallInt 0
      | some keyBits =>
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              throw e
          | .ok (none, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              VM.pushSmallInt 0
          | .ok (some valueSlice, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              if byRef then
                if valueSlice.bitsRemaining == 0 && valueSlice.refsRemaining == 1 then
                  let c := valueSlice.cell.refs[valueSlice.refPos]!
                  VM.push (.cell c)
                  VM.pushSmallInt (-1)
                else
                  throw .dictErr
              else
                VM.push (.slice valueSlice)
                VM.pushSmallInt (-1)
  | .dictSet intKey unsigned byRef mode =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd

      if byRef then
        let valRef ← VM.popCell
        match dictSetRefWithCells dictCell? keyBits valRef mode with
        | .error e =>
            throw e
        | .ok (newRoot?, ok, created, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            if created > 0 then
              modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
            match newRoot? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
            if mode == .set then
              if !ok then
                throw .fatal
            else
              VM.pushSmallInt (if ok then -1 else 0)
      else
        let valSlice ← VM.popSlice
        match dictSetSliceWithCells dictCell? keyBits valSlice mode with
        | .error e =>
            throw e
        | .ok (newRoot?, ok, created, loaded) =>
            for c in loaded do
              modify fun st => st.registerCellLoad c
            if created > 0 then
              modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
            match newRoot? with
            | none => VM.push .null
            | some c => VM.push (.cell c)
            if mode == .set then
              if !ok then
                throw .fatal
            else
              VM.pushSmallInt (if ok then -1 else 0)
  | .dictReplaceB intKey unsigned =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd
      let newVal ← VM.popBuilder
      match dictReplaceBuilderWithCells dictCell? keyBits newVal with
      | .error e =>
          throw e
      | .ok (newRoot?, ok, created, loaded) =>
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
          match newRoot? with
          | none => VM.push .null
          | some c => VM.push (.cell c)
          VM.pushSmallInt (if ok then -1 else 0)
  | .dictGetExec unsigned doCall pushZ =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let idx ← VM.popIntFinite
      match dictKeyBits? idx n unsigned with
      | none =>
          if pushZ then
            VM.push (.int (.num idx))
          else
            pure ()
      | some keyBits =>
          match dictLookupWithCells dictCell? keyBits with
          | .error e =>
              throw e
          | .ok (res?, loaded) =>
              for c in loaded do
                modify fun st => st.registerCellLoad c
              match res? with
              | none =>
                  if pushZ then
                    VM.push (.int (.num idx))
                  else
                    pure ()
              | some valueSlice =>
                  let cont : Continuation := .ordinary valueSlice (.quit 0) OrdCregs.empty OrdCdata.empty
                  modify fun st =>
                    if doCall then
                      st.callTo cont
                    else
                      st.jumpTo cont
  | .lddict preload quiet =>
      let s ← VM.popSlice
      let ok : Bool :=
        if s.haveBits 1 then
          let present : Bool := (s.readBits 1)[0]!
          let needRefs : Nat := if present then 1 else 0
          s.haveRefs needRefs
        else
          false
      if !ok then
        if quiet then
          if !preload then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let present : Bool := (s.readBits 1)[0]!
        let needRefs : Nat := if present then 1 else 0
        if present then
          let c := s.cell.refs[s.refPos]!
          VM.push (.cell c)
        else
          VM.push .null
        if !preload then
          let s' : Slice := { s with bitPos := s.bitPos + 1, refPos := s.refPos + needRefs }
          VM.push (.slice s')
        if quiet then
          VM.pushSmallInt (-1)

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

structure TraceEntry where
  step : Nat
  event : String
  cp : Int
  cc_before : String
  cc_after : String
  gas_before : Int
  gas_after : Int
  stack_before : String
  stack_after : String
  deriving Repr

instance : Inhabited TraceEntry where
  default :=
    { step := 0
      event := ""
      cp := 0
      cc_before := ""
      cc_after := ""
      gas_before := 0
      gas_after := 0
      stack_before := ""
      stack_after := "" }

def stackStr (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def Stack.pretty (s : Stack) : String :=
  stackStr s

def Slice.peekByteHex (s : Slice) : String :=
  if s.haveBits 8 then
    let b := bitsToNat (s.readBits 8)
    let hex := String.mk (Nat.toDigits 16 b)
    let hex := if b < 16 then "0" ++ hex else hex
    s!"0x{hex}"
  else
    "<eof>"

def natToHexPad (n : Nat) (digits : Nat) : String :=
  let hex := String.mk (Nat.toDigits 16 n)
  if hex.length ≥ digits then
    hex
  else
    String.mk (List.replicate (digits - hex.length) '0') ++ hex

def Slice.peekWord16Hex (s : Slice) : String :=
  if s.haveBits 16 then
    s!"0x{natToHexPad (bitsToNat (s.readBits 16)) 4}"
  else
    "<eof>"

def VmState.ccSummary (cc : Continuation) : String :=
  match cc with
  | .quit n => s!"quit {n}"
  | .excQuit => "excquit"
  | .whileCond _ _ _ => "whileCond"
  | .whileBody _ _ _ => "whileBody"
  | .untilBody _ _ => "untilBody"
  | .ordinary code _ _ _ =>
      s!"ord(bitPos={code.bitPos},refPos={code.refPos},bitsRem={code.bitsRemaining},refsRem={code.refsRemaining},next8={code.peekByteHex},next16={code.peekWord16Hex})"

def VmState.outOfGasHalt (st : VmState) : StepResult :=
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  StepResult.halt Excno.outOfGas.toInt st'

def VmState.step (st : VmState) : StepResult :=
  match st.cc with
  | .quit n =>
      .halt (~~~ n) st
  | .excQuit =>
      let action : VM Int := do
        -- Match `pop_smallint_range(0xffff)` behavior closely enough for MVP.
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res, st') := (action.run st)
      let n : Int :=
        match res with
        | .ok n => n
        | .error e => e.toInt
      .halt (~~~ n) st'
  | .whileCond cond body after =>
      let action : VM Unit := do
        if (← VM.popBool) then
          modify fun st => { st with regs := { st.regs with c0 := .whileBody cond body after }, cc := body }
        else
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
      let (res, st') := (action.run st)
      match res with
      | .ok _ =>
          .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            stExcGas.outOfGasHalt
          else
            .continue stExcGas
  | .whileBody cond body after =>
      .continue { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | .untilBody body after =>
      let action : VM Unit := do
        if (← VM.popBool) then
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        else
          modify fun st => { st with cc := body }
      let (res, st') := (action.run st)
      match res with
      | .ok _ =>
          .continue st'
      | .error e =>
          let stExc := st'.throwException e.toInt
          let stExcGas := stExc.consumeGas exceptionGasPrice
          if decide (stExcGas.gas.gasRemaining < 0) then
            stExcGas.outOfGasHalt
          else
            .continue stExcGas
  | .ordinary code saved cregs cdata =>
      -- Apply pending continuation control regs (MVP: c0,c1,c2,c4,c5,c7), once.
      let st : VmState :=
        let regs0 := st.regs
        let regs1 := match cregs.c0 with | some c0 => { regs0 with c0 := c0 } | none => regs0
        let regs2 := match cregs.c1 with | some c1 => { regs1 with c1 := c1 } | none => regs1
        let regs3 := match cregs.c2 with | some c2 => { regs2 with c2 := c2 } | none => regs2
        let regs4 := match cregs.c4 with | some c4 => { regs3 with c4 := c4 } | none => regs3
        let regs5 := match cregs.c5 with | some c5 => { regs4 with c5 := c5 } | none => regs4
        let regs6 := match cregs.c7 with | some c7 => { regs5 with c7 := c7 } | none => regs5
        let st1 : VmState := { st with regs := regs6 }
        let st2 : VmState :=
          if cdata.stack.isEmpty then
            st1
          else
            { st1 with stack := cdata.stack ++ st1.stack }
        let cdata' : OrdCdata := { cdata with stack := #[] }
        { st2 with cc := .ordinary code saved OrdCregs.empty cdata' }
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          -- Implicit RET.
          let st0 := st.consumeGas implicitRetGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            let (res, st1) := (VM.ret).run st0
            match res with
            | .ok _ =>
                .continue st1
            | .error e =>
                let stExc := st1.throwException e.toInt
                let stExcGas := stExc.consumeGas exceptionGasPrice
                if decide (stExcGas.gas.gasRemaining < 0) then
                  stExcGas.outOfGasHalt
                else
                  .continue stExcGas
        else
          -- Implicit JMPREF to the first reference.
          let st0 := st.consumeGas implicitJmpRefGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            if code.refPos < code.cell.refs.size then
              let refCell := code.cell.refs[code.refPos]!
              let st1 := st0.registerCellLoad refCell
              if decide (st1.gas.gasRemaining < 0) then
                st1.outOfGasHalt
              else
                .continue { st1 with cc := .ordinary (Slice.ofCell refCell) (.quit 0) OrdCregs.empty OrdCdata.empty }
            else
              let stExc := st0.throwException Excno.cellUnd.toInt
              let stExcGas := stExc.consumeGas exceptionGasPrice
              if decide (stExcGas.gas.gasRemaining < 0) then
                stExcGas.outOfGasHalt
              else
                .continue stExcGas
      else
        let decoded : Except Excno (Instr × Nat × Slice) :=
          if st.cp = 0 then
            decodeCp0WithBits code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            let st0 := st.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              .continue st0
        | .ok (instr, totBits, rest) =>
            let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
            let stGas := st0.consumeGas (instrGas instr totBits)
            if decide (stGas.gas.gasRemaining < 0) then
              stGas.outOfGasHalt
            else
              let (res, st1) := (execInstr instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    st1.outOfGasHalt
                  else
                    .continue st1
              | .error e =>
                  -- TVM behavior: convert VM errors into an exception jump to c2.
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    stExcGas.outOfGasHalt
                  else
                .continue stExcGas

def VmState.stepTrace (st : VmState) (step : Nat) : TraceEntry × StepResult :=
  let mk (event : String) (stAfter : VmState) (res : StepResult) : TraceEntry × StepResult :=
    ({ step
       event
       cp := st.cp
       cc_before := VmState.ccSummary st.cc
       cc_after := VmState.ccSummary stAfter.cc
       gas_before := st.gas.gasRemaining
       gas_after := stAfter.gas.gasRemaining
       stack_before := stackStr st.stack
       stack_after := stackStr stAfter.stack },
     res)
  match st.cc with
  | .quit n =>
      let res := StepResult.halt (~~~ n) st
      mk s!"quit({n})" st res
  | .excQuit =>
      let action : VM Int := do
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res0, st') := (action.run st)
      let n : Int :=
        match res0 with
        | .ok n => n
        | .error e => e.toInt
      let res := StepResult.halt (~~~ n) st'
      mk s!"excquit({n})" st' res
  | .whileCond cond body after =>
      let action : VM Bool := do
        let b ← VM.popBool
        if b then
          modify fun st => { st with regs := { st.regs with c0 := .whileBody cond body after }, cc := body }
        else
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        return b
      let (res0, st1) := (action.run st)
      let (event, res) :=
        match res0 with
        | .ok b => (s!"while_cond({b})", StepResult.continue st1)
        | .error e =>
            let stExc := st1.throwException e.toInt
            let stExcGas := stExc.consumeGas exceptionGasPrice
            if decide (stExcGas.gas.gasRemaining < 0) then
              (s!"while_cond_error({reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
            else
              (s!"while_cond_error({reprStr e})", StepResult.continue stExcGas)
      let stAfter :=
        match res with
        | .continue st' => st'
        | .halt _ st' => st'
      mk event stAfter res
  | .whileBody cond body after =>
      let st1 := { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
      let res := StepResult.continue st1
      mk "while_body" st1 res
  | .untilBody body after =>
      let action : VM Bool := do
        let b ← VM.popBool
        if b then
          match after with
          | .ordinary code saved cregs cdata =>
              modify fun st => { st with regs := { st.regs with c0 := saved }, cc := .ordinary code (.quit 0) cregs cdata }
          | _ =>
              modify fun st => { st with cc := after }
        else
          modify fun st => { st with cc := body }
        return b
      let (res0, st1) := (action.run st)
      let (event, res) :=
        match res0 with
        | .ok b => (s!"until_body({b})", StepResult.continue st1)
        | .error e =>
            let stExc := st1.throwException e.toInt
            let stExcGas := stExc.consumeGas exceptionGasPrice
            if decide (stExcGas.gas.gasRemaining < 0) then
              (s!"until_body_error({reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
            else
              (s!"until_body_error({reprStr e})", StepResult.continue stExcGas)
      let stAfter :=
        match res with
        | .continue st' => st'
        | .halt _ st' => st'
      mk event stAfter res
  | .ordinary code saved cregs cdata =>
      -- Apply pending continuation regs and closure stack (once), matching `VmState.step`.
      let st : VmState :=
        let regs0 := st.regs
        let regs1 := match cregs.c0 with | some c0 => { regs0 with c0 := c0 } | none => regs0
        let regs2 := match cregs.c1 with | some c1 => { regs1 with c1 := c1 } | none => regs1
        let regs3 := match cregs.c2 with | some c2 => { regs2 with c2 := c2 } | none => regs2
        let regs4 := match cregs.c4 with | some c4 => { regs3 with c4 := c4 } | none => regs3
        let regs5 := match cregs.c5 with | some c5 => { regs4 with c5 := c5 } | none => regs4
        let regs6 := match cregs.c7 with | some c7 => { regs5 with c7 := c7 } | none => regs5
        let st1 : VmState := { st with regs := regs6 }
        let st2 : VmState :=
          if cdata.stack.isEmpty then
            st1
          else
            { st1 with stack := cdata.stack ++ st1.stack }
        let cdata' : OrdCdata := { cdata with stack := #[] }
        { st2 with cc := .ordinary code saved OrdCregs.empty cdata' }
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          let st0 := st.consumeGas implicitRetGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              let (res0, st1) := (VM.ret).run st0
              match res0 with
              | .ok _ =>
                  .continue st1
              | .error e =>
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    stExcGas.outOfGasHalt
                  else
                    .continue stExcGas
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_ret" stAfter res
        else
          let st0 := st.consumeGas implicitJmpRefGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else if code.refPos < code.cell.refs.size then
              let refCell := code.cell.refs[code.refPos]!
              let st1 := st0.registerCellLoad refCell
              if decide (st1.gas.gasRemaining < 0) then
                st1.outOfGasHalt
              else
                .continue { st1 with cc := .ordinary (Slice.ofCell refCell) (.quit 0) OrdCregs.empty OrdCdata.empty }
            else
              let stExc := st0.throwException Excno.cellUnd.toInt
              let stExcGas := stExc.consumeGas exceptionGasPrice
              if decide (stExcGas.gas.gasRemaining < 0) then
                stExcGas.outOfGasHalt
              else
                .continue stExcGas
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_jmpref" stAfter res
      else
        let decoded : Except Excno (Instr × Nat × Slice) :=
          if st.cp = 0 then
            decodeCp0WithBits code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            let st0 := st.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            let res :=
              if decide (st0.gas.gasRemaining < 0) then
                st0.outOfGasHalt
              else
                .continue st0
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk s!"decode_error({e})" stAfter res
        | .ok (instr, totBits, rest) =>
            let st0 := { st with cc := .ordinary rest (.quit 0) OrdCregs.empty OrdCdata.empty }
            let stGas := st0.consumeGas (instrGas instr totBits)
            let (event, res) :=
              if decide (stGas.gas.gasRemaining < 0) then
                (s!"exec({instr.pretty}) out_of_gas", stGas.outOfGasHalt)
              else
                let (res1, st1) := (execInstr instr).run stGas
                match res1 with
                | .ok _ =>
                    if decide (st1.gas.gasRemaining < 0) then
                      (s!"exec({instr.pretty}) out_of_gas", st1.outOfGasHalt)
                    else
                      (s!"exec({instr.pretty})", .continue st1)
                | .error e =>
                    let stExc := st1.throwException e.toInt
                    let stExcGas := stExc.consumeGas exceptionGasPrice
                    if decide (stExcGas.gas.gasRemaining < 0) then
                      (s!"exec_error({instr.pretty},{reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
                    else
                      (s!"exec_error({instr.pretty},{reprStr e})", .continue stExcGas)
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk event stAfter res

def VmState.tryCommit (st : VmState) : Bool × VmState :=
  -- C++ also checks `level == 0`; our MVP has only ordinary cells (level 0).
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def VmState.runTrace (fuel : Nat) (st : VmState) (maxTrace : Nat := 200) :
    StepResult × Array TraceEntry × Bool :=
  Id.run do
    let mut stCur := st
    let mut fuelCur := fuel
    let mut step : Nat := 0
    let mut trace : Array TraceEntry := #[]
    let mut pos : Nat := 0
    let mut wrapped : Bool := false
    let mut res : StepResult := .continue stCur

    while fuelCur > 0 do
      let (entry, stepRes) := stCur.stepTrace step
      if maxTrace > 0 then
        if trace.size < maxTrace then
          trace := trace.push entry
        else
          trace := trace.set! pos entry
          pos := (pos + 1) % maxTrace
          wrapped := true

      match stepRes with
      | .continue st' =>
          stCur := st'
          res := .continue st'
          fuelCur := fuelCur - 1
          step := step + 1
      | .halt exitCode st' =>
          res := .halt exitCode st'
          stCur := st'
          fuelCur := 0

    match res with
    | .continue st' =>
        res := .halt (Excno.fatal.toInt) st'
    | .halt _ _ => pure ()

    -- Mirror the C++ commit wrapper shape; precise commit checks come later.
    let res' :=
      match res with
      | .continue st' => .halt (Excno.fatal.toInt) st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

    let traceOut :=
      if wrapped && trace.size > 0 then
        let n := trace.size
        Array.ofFn (n := n) fun i =>
          let idx := (pos + i.1) % n
          trace[idx]!
      else
        trace

    return (res', traceOut, wrapped)

def VmState.run (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step with
      | .continue st' => VmState.run fuel st'
      | .halt exitCode st' =>
          -- Mirror the C++ commit wrapper shape; precise commit checks come later.
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

/-! ### Proof scaffolding (Milestone 1, mostly `sorry`) -/

def WF_Int : IntVal → Prop
  | .nan => True
  | .num n =>
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      lo ≤ n ∧ n < hi

def WF_Cell (c : Cell) : Prop :=
  c.bits.size ≤ 1023 ∧ c.refs.size ≤ 4

def WF_Slice (s : Slice) : Prop :=
  WF_Cell s.cell ∧ s.bitPos ≤ s.cell.bits.size ∧ s.refPos ≤ s.cell.refs.size

def WF_Builder (b : Builder) : Prop :=
  b.bits.size ≤ 1023 ∧ b.refs.size ≤ 4

def WF_Tuple (t : Array Value) : Prop :=
  t.size ≤ 255

def WF_Value : Value → Prop
  | .int i => WF_Int i
  | .cell c => WF_Cell c
  | .slice s => WF_Slice s
  | .builder b => WF_Builder b
  | .tuple t => WF_Tuple t
  | .cont _ => True
  | .null => True

def WF_Gas (g : GasLimits) : Prop :=
  g.gasLimit ≤ g.gasMax ∧ g.gasBase = g.gasLimit + g.gasCredit ∧ g.gasRemaining ≤ g.gasBase

def WF_Regs (r : Regs) : Prop :=
  WF_Cell r.c4 ∧ WF_Cell r.c5 ∧ WF_Tuple r.c7

def WF_State (st : VmState) : Prop :=
  (∀ v ∈ st.stack.toList, WF_Value v) ∧ WF_Regs st.regs ∧ WF_Gas st.gas

theorem step_preserves_wf {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem run_preserves_wf {fuel : Nat} {st : VmState} :
    WF_State st →
      match VmState.run fuel st with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem step_progress {st : VmState} :
    WF_State st →
      match st.step with
      | .continue _ => True
      | .halt _ _ => True := by
  sorry

theorem step_gas_monotone {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining
      | .halt _ st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining := by
  sorry

end TvmLean
