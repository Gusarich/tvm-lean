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
  deriving DecidableEq, Repr, Inhabited

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

@[extern "tvmlean_hash_sha256"]
opaque hashSha256 (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_sha512"]
opaque hashSha512 (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_blake2b"]
opaque hashBlake2b (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_keccak256"]
opaque hashKeccak256 (data : ByteArray) : ByteArray

@[extern "tvmlean_hash_keccak512"]
opaque hashKeccak512 (data : ByteArray) : ByteArray

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

def IntVal.min (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (if a ≤ b then a else b)
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
  --
  -- NOTE: We avoid Lean's built-in `Int` division semantics here (which are not "truncate toward 0")
  -- because TVM explicitly needs floor/ceil/round-to-nearest variants.
  if y = 0 then
    0
  else
    let ax : Nat := (intAbs x).toNat
    let ay : Nat := (intAbs y).toNat
    let q : Nat := ax / ay
    let r : Nat := ax % ay
    let sx : Bool := decide (x < 0)
    let sy : Bool := decide (y < 0)
    if sx == sy then
      Int.ofNat q
    else
      if r = 0 then
        -Int.ofNat q
      else
        -Int.ofNat q - 1

def ceilDiv (x y : Int) : Int :=
  -- Ceil division (towards +∞), for non-zero `y`.
  if y = 0 then
    0
  else
    let ax : Nat := (intAbs x).toNat
    let ay : Nat := (intAbs y).toNat
    let q : Nat := ax / ay
    let r : Nat := ax % ay
    let sx : Bool := decide (x < 0)
    let sy : Bool := decide (y < 0)
    if sx == sy then
      if r = 0 then
        Int.ofNat q
      else
        Int.ofNat q + 1
    else
      -Int.ofNat q

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
  -- `special=true` means "exotic cell" in TON terminology.
  -- See TON Docs "Cells" + C++ `vm::DataCell` validation rules.
  special : Bool
  -- 3-bit level mask (0..7), as in TON `vm::Cell::LevelMask`.
  levelMask : Nat
  deriving Repr

inductive CellSpecialType where
  | ordinary
  | prunedBranch
  | library
  | merkleProof
  | merkleUpdate
  deriving Repr, DecidableEq

def CellSpecialType.ofByte? (b : Nat) : Option CellSpecialType :=
  match b with
  | 0 => some .ordinary
  | 1 => some .prunedBranch
  | 2 => some .library
  | 3 => some .merkleProof
  | 4 => some .merkleUpdate
  | _ => none

def Cell.maxLevel : Nat := 3

def LevelMask.getLevel (m : Nat) : Nat :=
  if m = 0 then 0 else Nat.log2 m + 1

def LevelMask.shiftRight (m : Nat) : Nat :=
  m >>> 1

def LevelMask.apply (m : Nat) (level : Nat) : Nat :=
  -- `mask & ((1<<level)-1)`; for level=0 this is always 0.
  if level = 0 then
    0
  else
    m &&& ((1 <<< level) - 1)

def LevelMask.isSignificant (m : Nat) (level : Nat) : Bool :=
  level = 0 || (((m >>> (level - 1)) &&& 1) = 1)

def LevelMask.popcount3 (m : Nat) : Nat :=
  (if (m &&& 1) = 1 then 1 else 0) +
  (if (m &&& 2) = 2 then 1 else 0) +
  (if (m &&& 4) = 4 then 1 else 0)

def LevelMask.getHashI (m : Nat) : Nat :=
  LevelMask.popcount3 m

def LevelMask.getHashesCount (m : Nat) : Nat :=
  LevelMask.getHashI m + 1

def Cell.computeOrdinaryLevelMask (refs : Array Cell) : Nat :=
  refs.foldl (fun acc r => acc ||| r.levelMask) 0

def Cell.mkOrdinary (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  { bits := bits, refs := refs, special := false, levelMask := Cell.computeOrdinaryLevelMask refs }

def Cell.empty : Cell :=
  Cell.mkOrdinary #[] #[]

instance : Inhabited Cell := ⟨Cell.empty⟩

partial def Cell.beq (a b : Cell) : Bool :=
  a.special == b.special &&
    a.levelMask == b.levelMask &&
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
  Cell.mkOrdinary (natToBits n bits) #[]

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

def bytesToNatLE (bs : Array UInt8) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    let mut shift : Nat := 0
    for b in bs do
      acc := acc + (b.toNat <<< shift)
      shift := shift + 8
    return acc

def byteArrayToNatBE (bs : ByteArray) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    for i in [0:bs.size] do
      acc := (acc <<< 8) + (bs.get! i).toNat
    return acc

structure BitByteAcc where
  bytes : Array UInt8 := #[]
  cur : Nat := 0
  curLen : Nat := 0
  deriving Repr

def BitByteAcc.empty : BitByteAcc := {}

def BitByteAcc.appendBit (acc : BitByteAcc) (b : Bool) : BitByteAcc :=
  let cur :=
    if b then
      acc.cur ||| (1 <<< (7 - acc.curLen))
    else
      acc.cur
  let curLen := acc.curLen + 1
  if curLen = 8 then
    { bytes := acc.bytes.push (UInt8.ofNat (cur &&& 0xff)), cur := 0, curLen := 0 }
  else
    { acc with cur, curLen }

def BitByteAcc.appendBits (acc : BitByteAcc) (bs : BitString) : BitByteAcc :=
  Id.run do
    let mut a := acc
    for b in bs do
      a := a.appendBit b
    return a

def BitByteAcc.finish (acc : BitByteAcc) : Except Excno (Array UInt8) := do
  if acc.curLen = 0 then
    return acc.bytes
  else
    throw .cellUnd

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

structure CellLevelInfo where
  ty : CellSpecialType
  levelMask : Nat
  effectiveLevel : Nat
  depths : Array Nat
  hashes : Array (Array UInt8)
  deriving Repr

def CellLevelInfo.clampLevel (info : CellLevelInfo) (level : Nat) : Nat :=
  Nat.min info.effectiveLevel (Nat.min Cell.maxLevel level)

def CellLevelInfo.getDepth (info : CellLevelInfo) (level : Nat) : Nat :=
  info.depths[info.clampLevel level]!

def CellLevelInfo.getHash (info : CellLevelInfo) (level : Nat) : Array UInt8 :=
  info.hashes[info.clampLevel level]!

def readDepthBE (data : Array UInt8) (off : Nat) : Except String Nat := do
  if off + 2 > data.size then
    throw "depth read out of bounds"
  return ((data[off]!.toNat <<< 8) + data[off + 1]!.toNat)

partial def Cell.computeLevelInfo? (c : Cell) : Except String CellLevelInfo := do
  if c.refs.size > 4 then
    throw "Too many references"
  if c.bits.size > 1023 then
    throw "Too many data bits"

  let mut childInfos : Array CellLevelInfo := #[]
  for r in c.refs do
    childInfos := childInfos.push (← Cell.computeLevelInfo? r)

  let ty : CellSpecialType ←
    if !c.special then
      pure .ordinary
    else
      if c.bits.size < 8 then
        throw "Not enough data for a special cell"
      let tyByte := bitsToNat (c.bits.take 8)
      match CellSpecialType.ofByte? tyByte with
      | some .ordinary => throw "Invalid special cell type"
      | some t => pure t
      | none => throw "Invalid special cell type"

  let maxLevel : Nat := Cell.maxLevel
  let mut levelMask : Nat := 0
  let mut depths : Array Nat := Array.replicate (maxLevel + 1) 0

  let mut prunedBytes : Option (Array UInt8) := none
  let mut prunedHashesCount : Nat := 0

  match ty with
  | .ordinary =>
      for ci in childInfos do
        levelMask := levelMask ||| ci.levelMask
        for lvl in [0:maxLevel + 1] do
          let d := ci.getDepth lvl
          if d > depths[lvl]! then
            depths := depths.set! lvl d
      if c.refs.size != 0 then
        depths := depths.map (fun d => d + 1)
  | .prunedBranch =>
      if c.refs.size != 0 then
        throw "Pruned branch cannot have references"
      if c.bits.size < 16 then
        throw "Length mismatch in a pruned branch"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a pruned branch"
      let bytes := bitStringToBytesBE c.bits
      prunedBytes := some bytes
      if bytes.size < 2 then
        throw "Not enough data for a special cell"
      levelMask := bytes[1]!.toNat
      let lvl := LevelMask.getLevel levelMask
      if lvl = 0 || lvl > maxLevel then
        throw "Invalid level mask in a pruned branch"
      prunedHashesCount := LevelMask.getHashI levelMask
      let expectedBytes : Nat := 2 + prunedHashesCount * (32 + 2)
      if bytes.size != expectedBytes then
        throw "Length mismatch in a pruned branch"
      -- depth[maxLevel] = 0
      for off in [0:maxLevel] do
        let i := maxLevel - 1 - off
        if LevelMask.isSignificant levelMask (i + 1) then
          let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask i)
          let depthOff := 2 + prunedHashesCount * 32 + hashesBefore * 2
          let d ← readDepthBE bytes depthOff
          depths := depths.set! i d
        else
          depths := depths.set! i (depths[i + 1]!)
  | .library =>
      if c.refs.size != 0 then
        throw "Library cell cannot have references"
      if c.bits.size != 8 * (1 + 32) then
        throw "Length mismatch in a library cell"
      levelMask := 0
      depths := Array.replicate (maxLevel + 1) 0
  | .merkleProof =>
      if c.refs.size != 1 then
        throw "Merkle proof must have exactly one reference"
      if c.bits.size != 8 * (1 + 32 + 2) then
        throw "Length mismatch in a Merkle proof"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle proof"
      let bytes := bitStringToBytesBE c.bits
      let child ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child)"
      let storedHash := bytes.extract 1 (1 + 32)
      if storedHash != child.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth ← readDepthBE bytes (1 + 32)
      if storedDepth != child.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in [0:maxLevel + 1] do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (child.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight child.levelMask
  | .merkleUpdate =>
      if c.refs.size != 2 then
        throw "Merkle update must have exactly two references"
      if c.bits.size != 8 * (1 + (32 + 2) * 2) then
        throw "Length mismatch in a Merkle update"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle update"
      let bytes := bitStringToBytesBE c.bits
      let c0 ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 0)"
      let c1 ←
        match childInfos[1]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 1)"
      let storedHash0 := bytes.extract 1 (1 + 32)
      if storedHash0 != c0.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedHash1 := bytes.extract (1 + 32) (1 + 2 * 32)
      if storedHash1 != c1.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth0 ← readDepthBE bytes (1 + 2 * 32)
      if storedDepth0 != c0.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      let storedDepth1 ← readDepthBE bytes (1 + 2 * 32 + 2)
      if storedDepth1 != c1.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in [0:maxLevel + 1] do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (c0.getDepth childLevel + 1))
        depths := depths.set! lvl (Nat.max depths[lvl]! (c1.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight (c0.levelMask ||| c1.levelMask)

  if c.levelMask != levelMask then
    throw "level mask mismatch"

  let effectiveLevel := LevelMask.getLevel levelMask
  if effectiveLevel > maxLevel then
    throw "Invalid level mask"

  let zeroHash : Array UInt8 := Array.replicate 32 0
  let mut hashes : Array (Array UInt8) := Array.replicate (maxLevel + 1) zeroHash
  let mut lastComputed : Option Nat := none

  let isMerkleNode : Bool := ty == .merkleProof || ty == .merkleUpdate

  for lvl in [0:maxLevel + 1] do
    let shouldCompute : Bool :=
      lvl == maxLevel || LevelMask.isSignificant levelMask (lvl + 1)
    if !shouldCompute then
      continue

    let h : Array UInt8 ←
      match ty, prunedBytes with
      | .prunedBranch, some bytes =>
          if lvl != maxLevel then
            let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask lvl)
            let off := 2 + hashesBefore * 32
            if off + 32 > bytes.size then
              throw "Length mismatch in a pruned branch"
            pure (bytes.extract off (off + 32))
          else
            -- computed below as an ordinary hash (no chaining for pruned branches)
            pure #[] -- placeholder, overwritten below
      | _, _ =>
          pure #[] -- placeholder, overwritten below

    let h :=
      if h.isEmpty then
        let refsCnt : Nat := c.refs.size
        let bitLen : Nat := c.bits.size
        let fullBytes : Nat := bitLen / 8
        let remBits : Nat := bitLen % 8
        let d1 : Nat :=
          refsCnt +
            (if c.special then 8 else 0) +
              (LevelMask.apply levelMask lvl <<< 5)
        let d2 : Nat := (fullBytes <<< 1) + (if remBits = 0 then 0 else 1)
        Id.run do
          let mut msg : Array UInt8 := #[UInt8.ofNat d1, UInt8.ofNat d2]
          match lastComputed with
          | some last =>
              if ty != .prunedBranch then
                msg := msg ++ hashes[last]!
              else
                -- pruned branch: no chaining; always hash original data
                for i in [0:fullBytes] do
                  msg := msg.push (bitsToByte c.bits (i * 8) 8)
                if remBits ≠ 0 then
                  msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)
          | none =>
              for i in [0:fullBytes] do
                msg := msg.push (bitsToByte c.bits (i * 8) 8)
              if remBits ≠ 0 then
                msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)

          let childLevel : Nat := if isMerkleNode then Nat.min maxLevel (lvl + 1) else lvl
          for ci in childInfos do
            let d := ci.getDepth childLevel
            msg := msg.push (UInt8.ofNat ((d >>> 8) &&& 0xff))
            msg := msg.push (UInt8.ofNat (d &&& 0xff))
          for ci in childInfos do
            msg := msg ++ ci.getHash childLevel
          sha256Digest msg
      else
        h

    -- Store + fill gaps.
    let start : Nat :=
      match lastComputed with
      | none => 0
      | some last => last + 1
    for j in [start:lvl] do
      hashes := hashes.set! j h
    hashes := hashes.set! lvl h
    lastComputed := some lvl

  return { ty, levelMask, effectiveLevel, depths, hashes }

partial def Cell.depth (c : Cell) : Nat :=
  match c.computeLevelInfo? with
  | .ok info => info.getDepth Cell.maxLevel
  | .error _ => 0

partial def Cell.hashBytes (c : Cell) : Array UInt8 :=
  match c.computeLevelInfo? with
  | .ok info => info.getHash Cell.maxLevel
  | .error _ => Array.replicate 32 0

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
  Cell.mkOrdinary
    (s.cell.bits.extract s.bitPos s.cell.bits.size)
    (s.cell.refs.extract s.refPos s.cell.refs.size)

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
  Cell.mkOrdinary b.bits b.refs

inductive DictSetMode : Type
  | set
  | replace
  | add
  deriving DecidableEq, Repr

inductive TupleInstr : Type
  | mktuple (n : Nat) -- TUPLE <n>
  | index (idx : Nat) -- INDEX <idx>
  | index2 (i : Nat) (j : Nat) -- INDEX2 <i>,<j> (0..3 each)
  | index3 (i : Nat) (j : Nat) (k : Nat) -- INDEX3 <i>,<j>,<k> (0..3 each)
  | untuple (n : Nat) -- UNTUPLE <n>
  | unpackFirst (n : Nat) -- UNPACKFIRST <n>
  | explode (maxLen : Nat) -- EXPLODE <maxLen>
  | setIndex (idx : Nat) -- SETINDEX <idx>
  | indexQ (idx : Nat) -- INDEXQ <idx>
  | setIndexQ (idx : Nat) -- SETINDEXQ <idx>
  | mktupleVar          -- TUPLEVAR
  | indexVar            -- INDEXVAR
  | untupleVar          -- UNTUPLEVAR
  | unpackFirstVar      -- UNPACKFIRSTVAR
  | explodeVar          -- EXPLODEVAR
  | setIndexVar         -- SETINDEXVAR
  | indexVarQ           -- INDEXVARQ
  | setIndexVarQ        -- SETINDEXVARQ
  | tlen                -- TLEN
  | qtlen               -- QTLEN
  | isTuple             -- ISTUPLE
  | last                -- LAST
  | tpush             -- TPUSH
  | tpop              -- TPOP
  deriving Repr

inductive CellInstr : Type
  | subslice -- SUBSLICE
  | split (quiet : Bool) -- SPLIT / SPLITQ
  | pldRefVar -- PLDREFVAR
  | loadLeInt (unsigned : Bool) (bytes : Nat) (prefetch : Bool) (quiet : Bool) -- {P}LD{I,U}LE{4,8}{Q}
  | ldZeroes -- LDZEROES
  | ldOnes   -- LDONES
  | ldSame   -- LDSAME
  | sdepth   -- SDEPTH
  | clevel   -- CLEVEL
  | clevelMask -- CLEVELMASK
  | chashI (i : Nat) -- CHASHI <i>
  | cdepthI (i : Nat) -- CDEPTHI <i>
  | chashIX  -- CHASHIX (index from stack)
  | cdepthIX -- CDEPTHIX (index from stack)
  | schkBits (quiet : Bool) -- SCHKBITS / SCHKBITSQ
  | schkRefs (quiet : Bool) -- SCHKREFS / SCHKREFSQ
  | schkBitRefs (quiet : Bool) -- SCHKBITREFS / SCHKBITREFSQ
  | bdepth     -- BDEPTH
  | brefs      -- BREFS
  | bbitrefs   -- BBITREFS
  | brembits   -- BREMBITS
  | bremrefs   -- BREMREFS
  | brembitrefs -- BREMBITREFS
  | bchkBitsImm (bits : Nat) (quiet : Bool) -- BCHKBITS{Q} <bits>
  | bchk (needBits : Bool) (needRefs : Bool) (quiet : Bool) -- BCHK{BITS,REFS,BITREFS}{Q}
  deriving Repr

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
  | pu2xc (x : Nat) (y : Nat) (z : Nat) -- PU2XC s<x>,s<y-1>,s<z-2>
  | push2 (x : Nat) (y : Nat) -- PUSH2 s<x>,s<y>
  | push3 (x : Nat) (y : Nat) (z : Nat) -- PUSH3 s<x>,s<y>,s<z>
  | blkSwap (x : Nat) (y : Nat) -- BLKSWAP <x>,<y>
  | blkPush (x : Nat) (y : Nat) -- BLKPUSH <x>,<y>
  | rot                -- ROT
  | rotRev             -- ROTREV
  | twoSwap            -- 2SWAP
  | twoDup             -- 2DUP
  | twoOver            -- 2OVER
  | reverse (x : Nat) (y : Nat) -- REVERSE <x>,<y>
  | pick               -- PICK
  | roll               -- ROLL
  | rollRev            -- ROLLREV
  | blkSwapX           -- BLKSWX
  | reverseX           -- REVX
  | dropX              -- DROPX
  | xchgX              -- XCHGX
  | depth              -- DEPTH
  | chkDepth           -- CHKDEPTH
  | onlyTopX           -- ONLYTOPX
  | onlyX              -- ONLYX
  | tuck               -- TUCK
  | pushCtr (idx : Nat) -- PUSHCTRX <idx> (we'll use it for c4/c5/c7 too)
  | popCtr (idx : Nat)  -- POPCTRX <idx>
  | setContCtr (idx : Nat) -- SETCONTCTR c<idx>
  | ctos
  | xctos
  | newc
  | endc
  | endcst
  | ends
  | ldu (bits : Nat)
  | loadInt (unsigned : Bool) (prefetch : Bool) (quiet : Bool) (bits : Nat)
  | loadIntVar (unsigned : Bool) (prefetch : Bool) (quiet : Bool) -- {P}LD{I,U}X{Q}
  | ldref
  | ldrefRtos
  | pldRefIdx (idx : Nat) -- PLDREFIDX <idx>
  | loadSliceX (prefetch : Bool) (quiet : Bool) -- {PLD,LD}SLICEX{Q}
  | loadSliceFixed (prefetch : Bool) (quiet : Bool) (bits : Nat) -- {P}LDSLICE{Q} <bits>
  | sti (bits : Nat)
  | stu (bits : Nat)
  | stIntVar (unsigned : Bool) (rev : Bool) (quiet : Bool) -- ST{I,U}X{R}{Q}
  | stIntFixed (unsigned : Bool) (rev : Bool) (quiet : Bool) (bits : Nat) -- ST{I,U}{R}{Q} <bits>
  | stSlice (rev : Bool) (quiet : Bool) -- {STSLICE,STSLICER}{Q?}
  | stb (rev : Bool) (quiet : Bool) -- {STB,STBR}{Q?}
  | stbRef (rev : Bool) (quiet : Bool) -- {STBREF,STBREFR}{Q?} and ENDCST (8-bit)
  | stSliceConst (s : Slice) -- STSLICECONST (inline constant slice)
  | stZeroes -- STZEROES
  | stOnes   -- STONES
  | stSame   -- STSAME
  | stref -- STREF
  | strefq -- STREFQ
  | bbits -- BBITS
  | setcp (cp : Int)
  | ifret
  | ifnotret
  | if_         -- IF
  | ifnot       -- IFNOT
  | inc
  | qinc
  | dec
  | qdec
  | negate
  | qnegate
  | qpow2
  | add
  | qadd
  | addInt (n : Int) -- ADDINT <tinyint8>
  | sub
  | qsub
  | qsubr
  | subr
  | mulInt (n : Int) -- MULINT <tinyint8>
  | mul
  | qmul
  | min
  | max
  | qmax
  | minmax
  | qminmax
  | abs (quiet : Bool) -- ABS / QABS
  | bitsize -- BITSIZE
  | mulShrModConst (d : Nat) (roundMode : Int) (z : Nat) -- MUL{RSHIFT,MODPOW2,RSHIFTMOD}# <z>
  | divMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) -- {Q}{ADD}{DIV,MOD,DIVMOD}{R,C}
  | mulDivMod (d : Nat) (roundMode : Int) (add : Bool) (quiet : Bool) -- {Q}{MUL,MULADD}{DIV,MOD,DIVMOD}{R,C}
  | lshiftConst (quiet : Bool) (bits : Nat) -- {Q}LSHIFT <tinyint8+1>
  | rshiftConst (quiet : Bool) (bits : Nat) -- {Q}RSHIFT <tinyint8+1>
  | lshift            -- LSHIFT
  | rshift            -- RSHIFT
  | equal
  | neq
  | throw (exc : Int)      -- THROW <exc>
  | throwIf (exc : Int)    -- THROWIF <exc>
  | throwIfNot (exc : Int) -- THROWIFNOT <exc>
  | throwArg (exc : Int)      -- THROWARG <exc>
  | throwArgIf (exc : Int)    -- THROWARGIF <exc>
  | throwArgIfNot (exc : Int) -- THROWARGIFNOT <exc>
  | throwAny (hasParam : Bool) (hasCond : Bool) (throwCond : Bool) -- THROW{ARG}ANY{IF,IFNOT}
  | try_               -- TRY
  | saveCtr (idx : Nat)  -- SAVECTR c<idx>
  | sameAlt             -- SAMEALT
  | sameAltSave         -- SAMEALTSAVE
  | boolAnd             -- BOOLAND
  | boolOr              -- BOOLOR
  | composBoth          -- COMPOSBOTH
  | setContVarArgs      -- SETCONTVARARGS
  | dictPushConst (dict : Cell) (keyBits : Nat) -- DICTPUSHCONST: pushes dict-root cell + key size
  | dictGet (intKey : Bool) (unsigned : Bool) (byRef : Bool) -- DICT{I,U}GET{REF?} / DICTGET{REF?}
  | dictGetNear (args4 : Nat) -- DICTGET{NEXT,PREV}{EQ} and DICT{I,U}GET{NEXT,PREV}{EQ}
  | dictGetMinMax (args5 : Nat) -- DICT{I,U}{MIN,MAX,REMMIN,REMMAX}{REF?}
  | dictGetExec (unsigned : Bool) (doCall : Bool) (pushZ : Bool) -- DICT{I,U}GET{JMP,EXEC}{Z?}
  | dictSet (intKey : Bool) (unsigned : Bool) (byRef : Bool) (mode : DictSetMode) -- DICT{I,U}{SET,REPLACE,ADD}{REF?}
  | dictSetB (intKey : Bool) (unsigned : Bool) (mode : DictSetMode) -- DICT{I,U}{SET,REPLACE,ADD}B
  | dictReplaceB (intKey : Bool) (unsigned : Bool) -- DICT{I,U}?REPLACEB (builder value)
  | stdict              -- STDICT
  | skipdict            -- SKIPDICT
  | lddict (preload : Bool) (quiet : Bool) -- {P}LDDICT{Q}
  | and_
  | or
  | xor
  | not_
  | sgn
  | less
  | leq
  | greater
  | geq
  | cmp
  | qcmp
  | sbits
  | srefs
  | sbitrefs
  | cdepth             -- CDEPTH
  | sempty            -- SEMPTY
  | sdempty           -- SDEMPTY
  | srempty           -- SREMPTY
  | sdCntLead0         -- SDCNTLEAD0
  | sdCntTrail0        -- SDCNTTRAIL0
  | sdEq              -- SDEQ
  | sdPpfx            -- SDPPFX
  | sdPfx             -- SDPFX
  | sdPfxRev          -- SDPFXREV
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
  | nullSwapIf        -- NULLSWAPIF
  | nullSwapIfNot     -- NULLSWAPIFNOT
  | nullRotrIf        -- NULLROTRIF
  | nullRotrIfNot     -- NULLROTRIFNOT
  | nullSwapIf2       -- NULLSWAPIF2
  | nullSwapIfNot2    -- NULLSWAPIFNOT2
  | nullRotrIf2       -- NULLROTRIF2
  | nullRotrIfNot2    -- NULLROTRIFNOT2
  | tupleOp (op : TupleInstr)
  | cellOp (op : CellInstr)
  | blkdrop2 (x : Nat) (y : Nat) -- BLKDROP2 <x>,<y>
  | pushSliceConst (s : Slice) -- PUSHSLICE (inline constant slice)
  | pushCont (code : Slice) -- PUSHCONT (inline continuation)
  | pushRef (c : Cell) -- PUSHREF (1 ref)
  | pushRefSlice (c : Cell) -- PUSHREFSLICE (1 ref)
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
  | prepareDict (idx : Nat)    -- PREPAREDICT <idx>
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
  | globalId             -- GLOBALID
  | getGasFee            -- GETGASFEE
  | getStorageFee        -- GETSTORAGEFEE
  | getGasFeeSimple      -- GETGASFEESIMPLE
  | getForwardFee          -- GETFORWARDFEE
  | getPrecompiledGas   -- GETPRECOMPILEDGAS
  | getOriginalFwdFee  -- GETORIGINALFWDFEE
  | getForwardFeeSimple    -- GETFORWARDFEESIMPLE
  | inMsgParam (idx : Nat) -- INMSG_* / INMSGPARAM <idx>
  | hashExt (hashId : Nat) (append : Bool) (rev : Bool) -- HASHEXT{A}{R} <hashId> (255 means from stack)
  | hashCU             -- HASHCU
  | hashSU             -- HASHSU
  | chkSignU           -- CHKSIGNU
  | chkSignS           -- CHKSIGNS
  | sendMsg            -- SENDMSG
  | sendRawMsg         -- SENDRAWMSG
  | rawReserve         -- RAWRESERVE
  | rawReserveX        -- RAWRESERVEX
  | setCode            -- SETCODE
  deriving Repr

def TupleInstr.pretty : TupleInstr → String
  | .mktuple n => s!"TUPLE {n}"
  | .index idx => s!"INDEX {idx}"
  | .index2 i j => s!"INDEX2 {i},{j}"
  | .index3 i j k => s!"INDEX3 {i},{j},{k}"
  | .untuple n => s!"UNTUPLE {n}"
  | .unpackFirst n => s!"UNPACKFIRST {n}"
  | .explode maxLen => s!"EXPLODE {maxLen}"
  | .setIndex idx => s!"SETINDEX {idx}"
  | .indexQ idx => s!"INDEXQ {idx}"
  | .setIndexQ idx => s!"SETINDEXQ {idx}"
  | .mktupleVar => "TUPLEVAR"
  | .indexVar => "INDEXVAR"
  | .untupleVar => "UNTUPLEVAR"
  | .unpackFirstVar => "UNPACKFIRSTVAR"
  | .explodeVar => "EXPLODEVAR"
  | .setIndexVar => "SETINDEXVAR"
  | .indexVarQ => "INDEXVARQ"
  | .setIndexVarQ => "SETINDEXVARQ"
  | .tlen => "TLEN"
  | .qtlen => "QTLEN"
  | .isTuple => "ISTUPLE"
  | .last => "LAST"
  | .tpush => "TPUSH"
  | .tpop => "TPOP"

def CellInstr.pretty : CellInstr → String
  | .subslice => "SUBSLICE"
  | .split quiet => if quiet then "SPLITQ" else "SPLIT"
  | .pldRefVar => "PLDREFVAR"
  | .loadLeInt unsigned bytes prefetch quiet =>
      let p := if prefetch then "PLD" else "LD"
      let iu := if unsigned then "U" else "I"
      let q := if quiet then "Q" else ""
      s!"{p}{iu}LE{bytes}{q}"
  | .ldZeroes => "LDZEROES"
  | .ldOnes => "LDONES"
  | .ldSame => "LDSAME"
  | .sdepth => "SDEPTH"
  | .clevel => "CLEVEL"
  | .clevelMask => "CLEVELMASK"
  | .chashI i => s!"CHASHI {i}"
  | .cdepthI i => s!"CDEPTHI {i}"
  | .chashIX => "CHASHIX"
  | .cdepthIX => "CDEPTHIX"
  | .schkBits quiet => if quiet then "SCHKBITSQ" else "SCHKBITS"
  | .schkRefs quiet => if quiet then "SCHKREFSQ" else "SCHKREFS"
  | .schkBitRefs quiet => if quiet then "SCHKBITREFSQ" else "SCHKBITREFS"
  | .bdepth => "BDEPTH"
  | .brefs => "BREFS"
  | .bbitrefs => "BBITREFS"
  | .brembits => "BREMBITS"
  | .bremrefs => "BREMREFS"
  | .brembitrefs => "BREMBITREFS"
  | .bchkBitsImm bits quiet =>
      let q := if quiet then "Q" else ""
      s!"BCHKBITS{q} {bits}"
  | .bchk needBits needRefs quiet =>
      let kind :=
        if needBits && needRefs then "BCHKBITREFS"
        else if needBits then "BCHKBITS"
        else if needRefs then "BCHKREFS"
        else "BCHK"
      let q := if quiet then "Q" else ""
      s!"{kind}{q}"

def Instr.pretty : Instr → String
  | .nop => "NOP"
  | .pushInt .nan => "PUSHNAN"
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
  | .pu2xc x y z => s!"PU2XC {x},{Int.ofNat y - 1},{Int.ofNat z - 2}"
  | .push2 x y => s!"PUSH2 {x},{y}"
  | .push3 x y z => s!"PUSH3 {x},{y},{z}"
  | .blkSwap x y => s!"BLKSWAP {x},{y}"
  | .blkPush x y => s!"BLKPUSH {x},{y}"
  | .rot => "ROT"
  | .rotRev => "ROTREV"
  | .twoSwap => "2SWAP"
  | .twoDup => "2DUP"
  | .twoOver => "2OVER"
  | .reverse x y => s!"REVERSE {x},{y}"
  | .pick => "PICK"
  | .roll => "ROLL"
  | .rollRev => "ROLLREV"
  | .blkSwapX => "BLKSWX"
  | .reverseX => "REVX"
  | .dropX => "DROPX"
  | .xchgX => "XCHGX"
  | .depth => "DEPTH"
  | .chkDepth => "CHKDEPTH"
  | .onlyTopX => "ONLYTOPX"
  | .onlyX => "ONLYX"
  | .tuck => "TUCK"
  | .pushCtr idx => s!"PUSHCTR {idx}"
  | .popCtr idx => s!"POPCTR {idx}"
  | .setContCtr idx => s!"SETCONTCTR c{idx}"
  | .ctos => "CTOS"
  | .xctos => "XCTOS"
  | .newc => "NEWC"
  | .endc => "ENDC"
  | .endcst => "ENDCST"
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
  | .ldrefRtos => "LDREFRTOS"
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
  | .stb rev quiet =>
      let base := if rev then "STBR" else "STB"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stbRef rev quiet =>
      let base := if rev then "STBREFR" else "STBREF"
      let q := if quiet then "Q" else ""
      s!"{base}{q}"
  | .stSliceConst s => s!"STSLICECONST(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .stZeroes => "STZEROES"
  | .stOnes => "STONES"
  | .stSame => "STSAME"
  | .stref => "STREF"
  | .strefq => "STREFQ"
  | .bbits => "BBITS"
  | .setcp cp => s!"SETCP {cp}"
  | .ifret => "IFRET"
  | .ifnotret => "IFNOTRET"
  | .if_ => "IF"
  | .ifnot => "IFNOT"
  | .inc => "INC"
  | .qinc => "QINC"
  | .dec => "DEC"
  | .qdec => "QDEC"
  | .negate => "NEGATE"
  | .qnegate => "QNEGATE"
  | .qpow2 => "QPOW2"
  | .add => "ADD"
  | .qadd => "QADD"
  | .addInt n => s!"ADDINT {n}"
  | .sub => "SUB"
  | .qsub => "QSUB"
  | .qsubr => "QSUBR"
  | .subr => "SUBR"
  | .mulInt n => s!"MULINT {n}"
  | .mul => "MUL"
  | .qmul => "QMUL"
  | .min => "MIN"
  | .max => "MAX"
  | .qmax => "QMAX"
  | .minmax => "MINMAX"
  | .qminmax => "QMINMAX"
  | .abs quiet => if quiet then "QABS" else "ABS"
  | .bitsize => "BITSIZE"
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
  | .mulDivMod d roundMode addMode quiet =>
      let name :=
        (if addMode then "MULADD" else "MUL") ++
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
  | .dictGetNear args4 =>
      let iu := if (args4 &&& 8) = 8 then (if (args4 &&& 4) = 4 then "U" else "I") else ""
      let dir := if (args4 &&& 2) = 2 then "PREV" else "NEXT"
      let eq := if (args4 &&& 1) = 1 then "EQ" else ""
      s!"DICT{iu}GET{dir}{eq}"
  | .dictGetMinMax args5 =>
      let iu := if (args5 &&& 4) = 4 then (if (args5 &&& 2) = 2 then "U" else "I") else ""
      let rem := if (args5 &&& 16) = 16 then "REM" else ""
      let mm := if (args5 &&& 8) = 8 then "MAX" else "MIN"
      let r := if (args5 &&& 1) = 1 then "REF" else ""
      s!"DICT{iu}{rem}{mm}{r}"
  | .throw exc => s!"THROW {exc}"
  | .throwIf exc => s!"THROWIF {exc}"
  | .throwIfNot exc => s!"THROWIFNOT {exc}"
  | .throwArg exc => s!"THROWARG {exc}"
  | .throwArgIf exc => s!"THROWARGIF {exc}"
  | .throwArgIfNot exc => s!"THROWARGIFNOT {exc}"
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
  | .dictSetB intKey unsigned mode =>
      let iu := if intKey then (if unsigned then "U" else "I") else ""
      let name :=
        match mode with
        | .set => "SET"
        | .replace => "REPLACE"
        | .add => "ADD"
      s!"DICT{iu}{name}B"
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
  | .xor => "XOR"
  | .not_ => "NOT"
  | .sgn => "SGN"
  | .less => "LESS"
  | .leq => "LEQ"
  | .greater => "GREATER"
  | .geq => "GEQ"
  | .cmp => "CMP"
  | .qcmp => "QCMP"
  | .sbits => "SBITS"
  | .srefs => "SREFS"
  | .sbitrefs => "SBITREFS"
  | .cdepth => "CDEPTH"
  | .sempty => "SEMPTY"
  | .sdempty => "SDEMPTY"
  | .srempty => "SREMPTY"
  | .sdCntLead0 => "SDCNTLEAD0"
  | .sdCntTrail0 => "SDCNTTRAIL0"
  | .sdEq => "SDEQ"
  | .sdPpfx => "SDPPFX"
  | .sdPfx => "SDPFX"
  | .sdPfxRev => "SDPFXREV"
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
  | .nullSwapIf => "NULLSWAPIF"
  | .nullSwapIfNot => "NULLSWAPIFNOT"
  | .nullRotrIf => "NULLROTRIF"
  | .nullRotrIfNot => "NULLROTRIFNOT"
  | .nullSwapIf2 => "NULLSWAPIF2"
  | .nullSwapIfNot2 => "NULLSWAPIFNOT2"
  | .nullRotrIf2 => "NULLROTRIF2"
  | .nullRotrIfNot2 => "NULLROTRIFNOT2"
  | .tupleOp op => op.pretty
  | .cellOp op => op.pretty
  | .blkdrop2 x y => s!"BLKDROP2 {x},{y}"
  | .pushSliceConst s => s!"PUSHSLICE(bits={s.bitsRemaining},refs={s.refsRemaining})"
  | .pushCont code => s!"PUSHCONT(bits={code.bitsRemaining},refs={code.refsRemaining})"
  | .pushRef c => s!"PUSHREF(bits={c.bits.size},refs={c.refs.size})"
  | .pushRefSlice c => s!"PUSHREFSLICE(bits={c.bits.size},refs={c.refs.size})"
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
  | .prepareDict idx => s!"PREPAREDICT {idx}"
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
  | .globalId => "GLOBALID"
  | .getGasFee => "GETGASFEE"
  | .getStorageFee => "GETSTORAGEFEE"
  | .getGasFeeSimple => "GETGASFEESIMPLE"
  | .getForwardFee => "GETFORWARDFEE"
  | .getPrecompiledGas => "GETPRECOMPILEDGAS"
  | .getOriginalFwdFee => "GETORIGINALFWDFEE"
  | .getForwardFeeSimple => "GETFORWARDFEESIMPLE"
  | .inMsgParam idx =>
      match idx with
      | 0 => "INMSG_BOUNCE"
      | 1 => "INMSG_BOUNCED"
      | 2 => "INMSG_SRC"
      | 3 => "INMSG_FWDFEE"
      | 4 => "INMSG_LT"
      | 5 => "INMSG_UTIME"
      | 6 => "INMSG_ORIGVALUE"
      | 7 => "INMSG_VALUE"
      | 8 => "INMSG_VALUEEXTRA"
      | 9 => "INMSG_STATEINIT"
      | _ => s!"INMSGPARAM {idx}"
  | .hashExt hashId append rev =>
      let a := if append then "A" else ""
      let r := if rev then "R" else ""
      let idStr := if hashId = 255 then "-1" else toString hashId
      s!"HASHEXT{a}{r} {idStr}"
  | .hashCU => "HASHCU"
  | .hashSU => "HASHSU"
  | .chkSignU => "CHKSIGNU"
  | .chkSignS => "CHKSIGNS"
  | .sendMsg => "SENDMSG"
  | .sendRawMsg => "SENDRAWMSG"
  | .rawReserve => "RAWRESERVE"
  | .rawReserveX => "RAWRESERVEX"
  | .setCode => "SETCODE"

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
  | .strefq, .strefq => true
  | .setcp x, .setcp y => x == y
  | .ifret, .ifret => true
  | .ifnotret, .ifnotret => true
  | .if_, .if_ => true
  | .ifnot, .ifnot => true
  | .inc, .inc => true
  | .qinc, .qinc => true
  | .dec, .dec => true
  | .qdec, .qdec => true
  | .negate, .negate => true
  | .qnegate, .qnegate => true
  | .qpow2, .qpow2 => true
  | .add, .add => true
  | .sub, .sub => true
  | .qsub, .qsub => true
  | .qsubr, .qsubr => true
  | .subr, .subr => true
  | .mulInt x, .mulInt y => x == y
  | .mul, .mul => true
  | .qmul, .qmul => true
  | .min, .min => true
  | .max, .max => true
  | .qmax, .qmax => true
  | .minmax, .minmax => true
  | .bitsize, .bitsize => true
  | .qminmax, .qminmax => true
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
  | .qcmp, .qcmp => true
  | .sbits, .sbits => true
  | .srefs, .srefs => true
  | .sbitrefs, .sbitrefs => true
  | .sempty, .sempty => true
  | .sdempty, .sdempty => true
  | .srempty, .srempty => true
  | .sdCntTrail0, .sdCntTrail0 => true
  | .sdEq, .sdEq => true
  | .sdPpfx, .sdPpfx => true
  | .sdPfx, .sdPfx => true
  | .sdPfxRev, .sdPfxRev => true
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
    c3 : Option Continuation := none
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
    | envelope (ext : Continuation) (cregs : OrdCregs) (cdata : OrdCdata)
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
      | .envelope _ _ _ => "<cont:env>"
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
  | .envelope x _ _, .envelope y _ _ => Continuation.beq x y
  | .whileCond c1 b1 a1, .whileCond c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | .whileBody c1 b1 a1, .whileBody c2 b2 a2 =>
      Continuation.beq c1 c2 && Continuation.beq b1 b2 && Continuation.beq a1 a2
  | _, _ => false

instance : BEq Continuation := ⟨Continuation.beq⟩

  def Continuation.hasC0 : Continuation → Bool
  | .ordinary _ _ cregs _ => cregs.c0.isSome
  | .envelope _ cregs _ => cregs.c0.isSome
  | _ => false

def Continuation.forceCdata : Continuation → Continuation
  | .ordinary code saved cregs cdata => .ordinary code saved cregs cdata
  | .envelope ext cregs cdata => .envelope ext cregs cdata
  | k => .envelope k OrdCregs.empty OrdCdata.empty

def OrdCregs.defineFromValue (cregs : OrdCregs) (idx : Nat) (v : Value) : Except Excno OrdCregs := do
  match idx, v with
  | 0, .cont k =>
      match cregs.c0 with
      | none => pure { cregs with c0 := some k }
      | some _ => throw .typeChk
  | 1, .cont k =>
      match cregs.c1 with
      | none => pure { cregs with c1 := some k }
      | some _ => throw .typeChk
  | 2, .cont k =>
      match cregs.c2 with
      | none => pure { cregs with c2 := some k }
      | some _ => throw .typeChk
  | 3, .cont k =>
      match cregs.c3 with
      | none => pure { cregs with c3 := some k }
      | some _ => throw .typeChk
  | 4, .cell c =>
      match cregs.c4 with
      | none => pure { cregs with c4 := some c }
      | some _ => throw .typeChk
  | 5, .cell c =>
      match cregs.c5 with
      | none => pure { cregs with c5 := some c }
      | some _ => throw .typeChk
  | 7, .tuple t =>
      -- `define_c7` in C++ never fails; it just keeps the existing one if present.
      match cregs.c7 with
      | none => pure { cregs with c7 := some t }
      | some _ => pure cregs
  | _, _ =>
      throw .typeChk

def Continuation.defineCtr (k : Continuation) (idx : Nat) (v : Value) : Except Excno Continuation := do
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs ← cregs.defineFromValue idx v
      return .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs ← cregs.defineFromValue idx v
      return .envelope ext cregs cdata
  | _ =>
      -- unreachable (forceCdata makes it either .ordinary or .envelope)
      return k

def Continuation.defineC0 (k : Continuation) (c0 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c0 with | some _ => cregs | none => { cregs with c0 := some c0 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c0 with | some _ => cregs | none => { cregs with c0 := some c0 }
      .envelope ext cregs cdata
  | _ =>
      k

def Continuation.defineC1 (k : Continuation) (c1 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c1 with | some _ => cregs | none => { cregs with c1 := some c1 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c1 with | some _ => cregs | none => { cregs with c1 := some c1 }
      .envelope ext cregs cdata
  | _ =>
      k

def Continuation.defineC2 (k : Continuation) (c2 : Continuation) : Continuation :=
  let k := k.forceCdata
  match k with
  | .ordinary code saved cregs cdata =>
      let cregs := match cregs.c2 with | some _ => cregs | none => { cregs with c2 := some c2 }
      .ordinary code saved cregs cdata
  | .envelope ext cregs cdata =>
      let cregs := match cregs.c2 with | some _ => cregs | none => { cregs with c2 := some c2 }
      .envelope ext cregs cdata
  | _ =>
      k

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

def CallFrame.identity : CallFrame := { savedStack := #[], retArgs := -1 }

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

def GasLimits.ofLimits (limit max credit : Int) : GasLimits :=
  let base : Int := limit + credit
  { gasMax := max
    gasLimit := limit
    gasCredit := credit
    gasRemaining := base
    gasBase := base }

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
def hashExtEntryGasPrice : Int := 1
def chksgnFreeCount : Nat := 10
def chksgnGasPrice : Int := 4000

def instrGas (i : Instr) (totBits : Nat) : Int :=
  let base : Int := gasPerInstr + Int.ofNat totBits
  match i with
  | .endc => base + cellCreateGasPrice
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
    let codeCell : Cell := Cell.mkOrdinary codeBits #[]
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

    -- THROWARG / THROWARGIF / THROWARGIFNOT: 13-bit prefix (0xf2c8 / 0xf2d8 / 0xf2e8 >> 3) + 11-bit excno.
    if p13 = (0xf2c8 >>> 3) ∨ p13 = (0xf2d8 >>> 3) ∨ p13 = (0xf2e8 >>> 3) then
      let (_, s13) ← s.takeBitsAsNat 13
      let (exc, s24) ← s13.takeBitsAsNat 11
      let e : Int := Int.ofNat exc
      if p13 = (0xf2c8 >>> 3) then
        return (.throwArg e, 24, s24)
      else if p13 = (0xf2d8 >>> 3) then
        return (.throwArgIf e, 24, s24)
      else
        return (.throwArgIfNot e, 24, s24)

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
      let cell : Cell := Cell.mkOrdinary bits #[]
      return (.sdBeginsConst quiet (Slice.ofCell cell), 21, rest)

  -- DICTPUSHCONST (24-bit, +1 ref): 0xf4a4..0xf4a7 + 10-bit key size.
  if s.haveBits 24 then
    let w24 := bitsToNat (s.readBits 24)
    -- BCHKBITS / BCHKBITSQ (24-bit): 16-bit opcode 0xcf38/0xcf3c + 8-bit arg (bits-1).
    let p16 := w24 >>> 8
    if p16 = 0xcf38 ∨ p16 = 0xcf3c then
      let bits : Nat := (w24 &&& 0xff) + 1
      let quiet : Bool := p16 = 0xcf3c
      let (_, s24) ← s.takeBitsAsNat 24
      return (.cellOp (.bchkBitsImm bits quiet), 24, s24)

    -- GETPARAMLONG / INMSGPARAMS (24-bit): 0xf88100..0xf881ff.
    if w24 >>> 8 = 0xf881 then
      let idx : Nat := w24 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.getParam idx, 24, s24)
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

    -- PREPAREDICT <idx> (24-bit): 10-bit prefix (0xf180 >> 6) + 14-bit args.
    -- Matches C++ `exec_preparedict` (contops.cpp).
    let p10 := w24 >>> 14
    if p10 = (0xf180 >>> 6) then
      let idx : Nat := w24 &&& 0x3fff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.prepareDict idx, 24, s24)

    -- HASHEXT (24-bit): 14-bit prefix (0xf904 >> 2) + 10-bit args (hash_id8 + rev + append).
    -- Matches C++ `exec_hash_ext` / `dump_hash_ext` (TON version >= 4).
    let p14 := w24 >>> 10
    if p14 = (0xf904 >>> 2) then
      let args10 : Nat := w24 &&& 0x3ff
      let rev : Bool := ((args10 >>> 8) &&& 1) = 1
      let append : Bool := ((args10 >>> 9) &&& 1) = 1
      let hashId : Nat := args10 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.hashExt hashId append rev, 24, s24)

    -- {P}LDSLICE{Q} <bits> (24-bit): 14-bit prefix (0xd71c >> 2) + 10-bit args (flags2 + bits8).
    -- Matches C++ `exec_load_slice_fixed2`.
    if p14 = (0xd71c >>> 2) then
      let args10 : Nat := w24 &&& 0x3ff
      let flags2 : Nat := args10 >>> 8
      let bits : Nat := (args10 &&& 0xff) + 1
      let prefetch : Bool := (flags2 &&& 1) = 1
      let quiet : Bool := (flags2 &&& 2) = 2
      let (_, s24) ← s.takeBitsAsNat 24
      return (.loadSliceFixed prefetch quiet bits, 24, s24)

    -- QLSHIFT / QRSHIFT (24-bit): 16-bit opcode 0xb7aa/0xb7ab + 8-bit arg.
    if p16 = 0xb7aa then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.lshiftConst true bits, 24, s24)
    if p16 = 0xb7ab then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.rshiftConst true bits, 24, s24)
    if w24 = 0xb7b609 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.qmax, 24, s24)
    if w24 = 0xb7b60b then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.abs true, 24, s24)
    if w24 = 0xb7b60a then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.qminmax, 24, s24)

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
    if p12 = 0x546 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.pu2xc x y z, 24, s24)
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
      let codeCell : Cell := Cell.mkOrdinary codeBits contRefs
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
      let cell : Cell := Cell.mkOrdinary bits refCells
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
      let cell : Cell := Cell.mkOrdinary bits rs
      return (.stSliceConst (Slice.ofCell cell), 14, rest)

  let b8 ← s.peekBitsAsNat 8
  -- PUSHREF / PUSHREFSLICE: 0x88/0x89 (8) + 1 ref.
  if b8 = 0x88 then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRef c, 8, s')
  if b8 = 0x89 then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRefSlice c, 8, s')
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
    let cell : Cell := Cell.mkOrdinary bits #[]
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
    if w16 = 0xcf30 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bdepth, 16, s16)
    if w16 = 0xcf31 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bbits, 16, s16)
    if w16 = 0xcf32 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brefs, 16, s16)
    if w16 = 0xcf33 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bbitrefs, 16, s16)
    if w16 = 0xcf35 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brembits, 16, s16)
    if w16 = 0xcf36 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bremrefs, 16, s16)
    if w16 = 0xcf37 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brembitrefs, 16, s16)
    if w16 = 0xcf39 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true false false), 16, s16)
    if w16 = 0xcf3a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk false true false), 16, s16)
    if w16 = 0xcf3b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true true false), 16, s16)
    if w16 = 0xcf3d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true false true), 16, s16)
    if w16 = 0xcf3e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk false true true), 16, s16)
    if w16 = 0xcf3f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true true true), 16, s16)
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
    -- BLKPUSH: 0x5f10..0x5fff (8-bit args packed as nibbles).
    if w16 &&& 0xff00 = 0x5f00 ∧ (w16 &&& 0xff) ≥ 0x10 then
      let args8 : Nat := w16 &&& 0xff
      let x : Nat := (args8 >>> 4) &&& 0xf
      let y : Nat := args8 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkPush x y, 16, s16)
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
      return (.tupleOp (.mktuple n), 16, s16)
    -- INDEX (12-bit prefix 0x6f1 + 4-bit `i`).
    if w16 &&& 0xfff0 = 0x6f10 then
      let i : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index i), 16, s16)
    -- UNTUPLE (12-bit prefix 0x6f2 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f20 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.untuple n), 16, s16)
    -- UNPACKFIRST (12-bit prefix 0x6f3 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f30 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.unpackFirst n), 16, s16)
    -- EXPLODE (12-bit prefix 0x6f4 + 4-bit `max_len`).
    if w16 &&& 0xfff0 = 0x6f40 then
      let maxLen : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.explode maxLen), 16, s16)
    -- SETINDEX (12-bit prefix 0x6f5 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f50 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.setIndex idx), 16, s16)
    -- INDEXQ (12-bit prefix 0x6f6 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f60 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.indexQ idx), 16, s16)
    -- SETINDEXQ (12-bit prefix 0x6f7 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f70 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.setIndexQ idx), 16, s16)

    -- TUPLEVAR / INDEXVAR / UNTUPLEVAR / UNPACKFIRSTVAR / EXPLODEVAR / SETINDEXVAR / INDEXVARQ / SETINDEXVARQ.
    if 0x6f80 ≤ w16 ∧ w16 ≤ 0x6f87 then
      let (_, s16) ← s.takeBitsAsNat 16
      match w16 with
      | 0x6f80 => return (.tupleOp .mktupleVar, 16, s16)
      | 0x6f81 => return (.tupleOp .indexVar, 16, s16)
      | 0x6f82 => return (.tupleOp .untupleVar, 16, s16)
      | 0x6f83 => return (.tupleOp .unpackFirstVar, 16, s16)
      | 0x6f84 => return (.tupleOp .explodeVar, 16, s16)
      | 0x6f85 => return (.tupleOp .setIndexVar, 16, s16)
      | 0x6f86 => return (.tupleOp .indexVarQ, 16, s16)
      | _ => return (.tupleOp .setIndexVarQ, 16, s16)

    -- TLEN / QTLEN / ISTUPLE / LAST / TPUSH / TPOP.
    if 0x6f88 ≤ w16 ∧ w16 ≤ 0x6f8d then
      let (_, s16) ← s.takeBitsAsNat 16
      match w16 with
      | 0x6f88 => return (.tupleOp .tlen, 16, s16)
      | 0x6f89 => return (.tupleOp .qtlen, 16, s16)
      | 0x6f8a => return (.tupleOp .isTuple, 16, s16)
      | 0x6f8b => return (.tupleOp .last, 16, s16)
      | 0x6f8c => return (.tupleOp .tpush, 16, s16)
      | _ => return (.tupleOp .tpop, 16, s16)

    -- INDEX2 (12-bit prefix 0x6fb + 4-bit args).
    if w16 &&& 0xfff0 = 0x6fb0 then
      let args4 : Nat := w16 &&& 0xf
      let i : Nat := (args4 >>> 2) &&& 3
      let j : Nat := args4 &&& 3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index2 i j), 16, s16)

    -- INDEX3 (10-bit prefix 0x6fc>>2 + 6-bit args).
    if w16 &&& 0xffc0 = 0x6fc0 then
      let args6 : Nat := w16 &&& 0x3f
      let i : Nat := (args6 >>> 4) &&& 3
      let j : Nat := (args6 >>> 2) &&& 3
      let k : Nat := args6 &&& 3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index3 i j k), 16, s16)
    if w16 = 0x6fa0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIf, 16, s16)
    if w16 = 0x6fa1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIfNot, 16, s16)
    if w16 = 0x6fa2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIf, 16, s16)
    if w16 = 0x6fa3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIfNot, 16, s16)
    if w16 = 0x6fa4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIf2, 16, s16)
    if w16 = 0x6fa5 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIfNot2, 16, s16)
    if w16 = 0x6fa6 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIf2, 16, s16)
    if w16 = 0x6fa7 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIfNot2, 16, s16)
    if w16 = 0xc700 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sempty, 16, s16)
    if w16 = 0xc701 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdempty, 16, s16)
    if w16 = 0xc702 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.srempty, 16, s16)
    if w16 = 0xc710 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdCntLead0, 16, s16)
    if w16 = 0xc712 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdCntTrail0, 16, s16)
    if w16 = 0xc705 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdEq, 16, s16)
    if w16 = 0xc708 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPfx, 16, s16)
    if w16 = 0xc709 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPfxRev, 16, s16)
    if w16 = 0xc70a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPpfx, 16, s16)
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
    if w16 = 0xb602 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bitsize, 16, s16)
    if w16 = 0xb60b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.abs false, 16, s16)
    if w16 = 0xb7a0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qadd, 16, s16)
    if w16 = 0xb7a1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qsub, 16, s16)
    if w16 = 0xb7a2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qsubr, 16, s16)
    if w16 = 0xb7a8 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qmul, 16, s16)
    if w16 = 0xb7a3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qnegate, 16, s16)
    if w16 = 0xb7a4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qinc, 16, s16)
    if w16 = 0xb7a5 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qdec, 16, s16)
    if w16 = 0xb7ae then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qpow2, 16, s16)
    if w16 = 0xb7bf then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qcmp, 16, s16)
    -- PUSHPOW2 / PUSHNAN: 0x8300..0x83ff.
    if w16 &&& 0xff00 = 0x8300 then
      let (_, s16) ← s.takeBitsAsNat 16
      if w16 = 0x83ff then
        return (.pushInt .nan, 16, s16)
      else
        let exp : Nat := (w16 &&& 0xff) + 1
        return (.pushPow2 exp, 16, s16)
    -- LDSLICE <bits> (16-bit): 0xd6 (8) + <bits-1> (8).
    if w16 &&& 0xff00 = 0xd600 then
      let bits : Nat := (w16 &&& 0xff) + 1
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadSliceFixed false false bits, 16, s16)
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
    -- MUL{DIV,MOD,DIVMOD} family (16-bit): 12-bit prefix 0xa98 + 4-bit args.
    -- Matches C++ `exec_muldivmod` (arithops.cpp).
    if w16 >>> 4 = 0xa98 then
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
      return (.mulDivMod d roundMode add false, 16, s16)
    -- Store slice into builder (16-bit): STSLICE / STSLICER and quiet variants.
    if w16 = 0xcf12 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false false, 16, s16)
    if w16 = 0xcf11 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef false false, 16, s16)
    if w16 = 0xcf15 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef true false, 16, s16)
    if w16 = 0xcf16 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true false, 16, s16)
    if w16 = 0xcf1a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false true, 16, s16)
    if w16 = 0xcf1e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true true, 16, s16)
    if w16 = 0xcf13 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb false false, 16, s16)
    if w16 = 0xcf17 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb true false, 16, s16)
    if w16 = 0xcf19 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef false true, 16, s16)
    if w16 = 0xcf1d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef true true, 16, s16)
    if w16 = 0xcf1b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb false true, 16, s16)
    if w16 = 0xcf1f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb true true, 16, s16)
    if w16 = 0xcf18 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.strefq, 16, s16)
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
    if w16 = 0xf835 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.globalId, 16, s16)
    if w16 = 0xf836 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getGasFee, 16, s16)
    if w16 = 0xf837 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getStorageFee, 16, s16)
    if w16 = 0xf839 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getPrecompiledGas, 16, s16)
    if w16 = 0xf838 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getForwardFee, 16, s16)
    if w16 = 0xf83a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getOriginalFwdFee, 16, s16)
    if w16 = 0xf83b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getGasFeeSimple, 16, s16)
    if w16 = 0xf83c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.getForwardFeeSimple, 16, s16)
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
    if 0xf890 ≤ w16 ∧ w16 < 0xf8a0 then
      let idx : Nat := w16 - 0xf890
      let (_, s16) ← s.takeBitsAsNat 16
      return (.inMsgParam idx, 16, s16)
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
    if w16 = 0xfb03 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.rawReserveX, 16, s16)
    if w16 = 0xfb04 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setCode, 16, s16)
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

    -- DICT{I,U}?SETB (builder value): 0xf441..0xf443.
    if 0xf441 ≤ w16 ∧ w16 < 0xf444 then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictSetB intKey unsigned .set, 16, s16)

    -- DICT{I,U}?REPLACEB (builder value): 0xf449..0xf44b.
    if 0xf449 ≤ w16 ∧ w16 < 0xf44c then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictReplaceB intKey unsigned, 16, s16)

    -- DICTGET{NEXT,PREV}{EQ} and DICT{I,U}GET{NEXT,PREV}{EQ}: 0xf474..0xf47f.
    -- Matches C++ `exec_dict_getnear` (dictops.cpp).
    if 0xf474 ≤ w16 ∧ w16 < 0xf480 then
      let args4 : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetNear args4, 16, s16)

    -- DICT{I,U}{MIN,MAX,REMMIN,REMMAX}{REF?}: 0xf482..0xf487 / 0xf48a..0xf48f / 0xf492..0xf497 / 0xf49a..0xf49f.
    -- Matches C++ `exec_dict_getmin` (dictops.cpp).
    if (0xf482 ≤ w16 ∧ w16 < 0xf488) ∨ (0xf48a ≤ w16 ∧ w16 < 0xf490) ∨ (0xf492 ≤ w16 ∧ w16 < 0xf498) ∨
        (0xf49a ≤ w16 ∧ w16 < 0xf4a0) then
      let args5 : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetMinMax args5, 16, s16)

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
    if w16 = 0xd734 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .subslice, 16, s16)
    if w16 = 0xd736 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.split false), 16, s16)
    if w16 = 0xd737 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.split true), 16, s16)
    if w16 = 0xd741 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBits false), 16, s16)
    if w16 = 0xd742 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkRefs false), 16, s16)
    if w16 = 0xd743 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBitRefs false), 16, s16)
    if w16 = 0xd745 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBits true), 16, s16)
    if w16 = 0xd746 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkRefs true), 16, s16)
    if w16 = 0xd747 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBitRefs true), 16, s16)
    if w16 = 0xd748 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .pldRefVar, 16, s16)
    if w16 &&& 0xfff0 = 0xd750 then
      let args : Nat := w16 &&& 0xf
      let unsigned : Bool := (args &&& 1) = 1
      let bytes : Nat := if (args &&& 2) = 2 then 8 else 4
      let prefetch : Bool := (args &&& 4) = 4
      let quiet : Bool := (args &&& 8) = 8
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.loadLeInt unsigned bytes prefetch quiet), 16, s16)
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
    if w16 = 0xd760 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldZeroes, 16, s16)
    if w16 = 0xd761 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldOnes, 16, s16)
    if w16 = 0xd762 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldSame, 16, s16)
    if w16 = 0xd764 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdepth, 16, s16)
    if w16 = 0xd765 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cdepth, 16, s16)
    if w16 = 0xd766 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .clevel, 16, s16)
    if w16 = 0xd767 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .clevelMask, 16, s16)
    if w16 &&& 0xfffc = 0xd768 then
      let i : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.chashI i), 16, s16)
    if w16 &&& 0xfffc = 0xd76c then
      let i : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.cdepthI i), 16, s16)
    if w16 = 0xd770 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .chashIX, 16, s16)
    if w16 = 0xd771 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .cdepthIX, 16, s16)

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
  if b8 = 0x5c then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoDup, 8, s')
  if b8 = 0x5d then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoOver, 8, s')
  if b8 = 0x5e then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := ((args >>> 4) &&& 0xf) + 2
    let y : Nat := args &&& 0xf
    return (.reverse x y, 16, s16)
  if b8 = 0x60 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pick, 8, s')
  if b8 = 0x61 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.roll, 8, s')
  if b8 = 0x62 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rollRev, 8, s')
  if b8 = 0x63 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.blkSwapX, 8, s')
  if b8 = 0x64 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.reverseX, 8, s')
  if b8 = 0x65 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.dropX, 8, s')
  if b8 = 0x66 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.tuck, 8, s')
  if b8 = 0x67 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchgX, 8, s')
  if b8 = 0x68 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.depth, 8, s')
  if b8 = 0x69 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.chkDepth, 8, s')
  if b8 = 0x6a then
    let (_, s') ← s.takeBitsAsNat 8
    return (.onlyTopX, 8, s')
  if b8 = 0x6b then
    let (_, s') ← s.takeBitsAsNat 8
    return (.onlyX, 8, s')
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
  if b8 = 0xb2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xor, 8, s')
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
  -- ENDCST: 0xcd (8). Alias for STBREFR (non-quiet).
  if b8 = 0xcd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.endcst, 8, s')
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
  if b8 = 0xd5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ldrefRtos, 8, s')
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
      -- addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9) workchain_id:int32 address:(bits addr_len)
      let s3 ← s2.skipMaybeAnycast
      let (len, s12) ← s3.takeBitsAsNatCellUnd 9
      let need : Nat := 32 + len
      if s12.haveBits need then
        return s12.advanceBits need
      else
        throw .cellUnd
  | _ =>
      throw .cellUnd

def Slice.takeVarUIntegerCellUnd (s : Slice) (lenBits : Nat) : Except Excno (Nat × Slice) := do
  let (len, s1) ← s.takeBitsAsNatCellUnd lenBits
  let dataBits : Nat := len * 8
  if s1.haveBits dataBits then
    let bs := s1.readBits dataBits
    return (bitsToNat bs, s1.advanceBits dataBits)
  else
    throw .cellUnd

def Slice.takeGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- Grams = VarUInteger 16, which uses 4-bit length (bytes) prefix in practice.
  let (n, s1) ← s.takeVarUIntegerCellUnd 4
  return (Int.ofNat n, s1)

def Slice.skipHashmapECellUnd (s : Slice) : Except Excno Slice := do
  -- HashmapE is encoded as: `hme_empty$0` or `hme_root$1 root:^Hashmap`.
  let (tag, s1) ← s.takeBitsAsNatCellUnd 1
  if tag = 0 then
    return s1
  else
    if s1.haveRefs 1 then
      return { s1 with refPos := s1.refPos + 1 }
    else
      throw .cellUnd

def Slice.takeCurrencyCollectionGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- CurrencyCollection = currencies$_ grams:Grams other:ExtraCurrencyCollection.
  let (grams, s1) ← s.takeGramsCellUnd
  -- ExtraCurrencyCollection = extra_currencies$_ dict:(HashmapE 32 (VarUInteger 32))
  let s2 ← s1.skipHashmapECellUnd
  return (grams, s2)

def Slice.skipStateInitCellUnd (s : Slice) : Except Excno Slice := do
  -- StateInit = _ fixed_prefix_length:(Maybe (## 5)) special:(Maybe TickTock)
  --              code:(Maybe ^Cell) data:(Maybe ^Cell) library:(Maybe ^Cell)
  let (hasFixed, s1) ← s.takeBitsAsNatCellUnd 1
  let s2 ←
    if hasFixed = 0 then
      pure s1
    else if s1.haveBits 5 then
      pure (s1.advanceBits 5)
    else
      throw .cellUnd
  let (hasSpecial, s3) ← s2.takeBitsAsNatCellUnd 1
  let s4 ←
    if hasSpecial = 0 then
      pure s3
    else if s3.haveBits 2 then
      pure (s3.advanceBits 2)
    else
      throw .cellUnd
  let (hasCode, s5) ← s4.takeBitsAsNatCellUnd 1
  let s6 ←
    if hasCode = 0 then
      pure s5
    else if s5.haveRefs 1 then
      pure { s5 with refPos := s5.refPos + 1 }
    else
      throw .cellUnd
  let (hasData, s7) ← s6.takeBitsAsNatCellUnd 1
  let s8 ←
    if hasData = 0 then
      pure s7
    else if s7.haveRefs 1 then
      pure { s7 with refPos := s7.refPos + 1 }
    else
      throw .cellUnd
  let (hasLib, s9) ← s8.takeBitsAsNatCellUnd 1
  if hasLib = 0 then
    return s9
  else if s9.haveRefs 1 then
    return { s9 with refPos := s9.refPos + 1 }
  else
    throw .cellUnd

def Slice.prefixCell (start stop : Slice) : Cell :=
  Cell.mkOrdinary
    (start.cell.bits.extract start.bitPos stop.bitPos)
    (start.cell.refs.extract start.refPos stop.refPos)

structure SendMsgParsed where
  extMsg : Bool
  dest : Slice
  value : Int
  userFwdFee : Int
  extraFlagsLen : Nat
  haveExtraCurrencies : Bool
  haveInit : Bool
  initRef : Bool
  initInlineBits : Nat
  initRefs : Nat
  bodyRef : Bool
  bodyInlineBits : Nat
  bodyRefs : Nat
  deriving Repr

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

def dictLabelBits (lbl : DictLabel) : BitString :=
  match lbl.sameBit with
  | some b => Array.replicate lbl.len b
  | none => lbl.remainder.readBits lbl.len

def bitsCommonPrefixLen (a b : BitString) : Nat :=
  let m : Nat := Nat.min a.size b.size
  Id.run do
    let mut k : Nat := 0
    while k < m && a[k]! == b[k]! do
      k := k + 1
    return k

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
    let newCell : Cell := Cell.mkOrdinary newBits newVal.refs
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
    let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
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

def builderAppendBuilderChecked (b : Builder) (v : Builder) : Except Excno Builder := do
  if b.canExtendBy v.bits.size v.refs.size then
    return { bits := b.bits ++ v.bits, refs := b.refs ++ v.refs }
  else
    throw .cellOv

partial def dictMinMaxAuxWithCells (cell : Cell) (n pos : Nat) (firstBit restBit : Bool) :
    Except Excno (Slice × BitString × Array Cell) := do
  let lbl ← parseDictLabel cell n
  let labelBits := dictLabelBits lbl
  let payload := lbl.remainder.advanceBits lbl.storedBits
  let rem0 : Nat := n - lbl.len
  if rem0 = 0 then
    return (payload, labelBits, #[cell])

  if cell.refs.size < 2 then
    throw .dictErr
  let posAfter : Nat := pos + lbl.len
  let bit : Bool := if posAfter = 0 then firstBit else restBit
  let child := cell.refs[if bit then 1 else 0]!
  let (val, keyTail, loaded) ← dictMinMaxAuxWithCells child (rem0 - 1) (posAfter + 1) firstBit restBit
  return (val, labelBits ++ #[bit] ++ keyTail, #[cell] ++ loaded)

def dictMinMaxWithCells (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      let (val, keyBits, loaded) ← dictMinMaxAuxWithCells cell n 0 firstBit restBit
      return (some (val, keyBits), loaded)

partial def dictNearestAuxWithCells (cell : Cell) (hint : BitString) (n pos : Nat) (allowEq : Bool)
    (firstBit restBit : Bool) : Except Excno (Option (Slice × BitString) × Array Cell) := do
  let lbl ← parseDictLabel cell n
  let labelBits := dictLabelBits lbl

  -- Compare the hint against the edge label.
  let pfxLen : Nat := bitsCommonPrefixLen labelBits (hint.take lbl.len)
  if pfxLen < lbl.len then
    let hintBit : Bool := hint[pfxLen]!
    let expectedBit : Bool := if pos = 0 ∧ pfxLen = 0 then firstBit else restBit
    if hintBit = expectedBit then
      return (none, #[cell])
    else
      let firstBit' : Bool := !firstBit
      let restBit' : Bool := !restBit
      let (val, keyBits, loadedMin) ← dictMinMaxAuxWithCells cell n pos firstBit' restBit'
      return (some (val, keyBits), #[cell] ++ loadedMin)

  -- Label fully matches: recurse into child.
  let payload := lbl.remainder.advanceBits lbl.storedBits
  let rem0 : Nat := n - lbl.len
  let posAfter : Nat := pos + lbl.len
  let hintRest : BitString := hint.extract lbl.len hint.size
  if rem0 = 0 then
    if allowEq then
      return (some (payload, labelBits), #[cell])
    else
      return (none, #[cell])

  if cell.refs.size < 2 then
    throw .dictErr
  if hintRest.isEmpty then
    throw .dictErr
  let bit : Bool := hintRest[0]!
  let child := cell.refs[if bit then 1 else 0]!
  let hintChild : BitString := hintRest.extract 1 hintRest.size
  let (resChild, loadedChild) ← dictNearestAuxWithCells child hintChild (rem0 - 1) (posAfter + 1) allowEq firstBit restBit
  match resChild with
  | some (val, keyTail) =>
      return (some (val, labelBits ++ #[bit] ++ keyTail), #[cell] ++ loadedChild)
  | none =>
      let expectedBit : Bool := if posAfter = 0 then firstBit else restBit
      if bit = expectedBit then
        return (none, #[cell] ++ loadedChild)
      else
        let altChild := cell.refs[if expectedBit then 1 else 0]!
        let firstBit' : Bool := !firstBit
        let restBit' : Bool := !restBit
        let (valAlt, keyAlt, loadedAlt) ← dictMinMaxAuxWithCells altChild (rem0 - 1) (posAfter + 1) firstBit' restBit'
        return (some (valAlt, labelBits ++ #[expectedBit] ++ keyAlt), #[cell] ++ loadedChild ++ loadedAlt)

def dictNearestWithCells (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchNext
      let firstBit : Bool := restBit != invertFirst
      dictNearestAuxWithCells cell hint hint.size 0 allowEq firstBit restBit

partial def dictDeleteAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  if !dictLabelMatches lbl key pos then
    return (none, some cell, 0, #[cell])
  let payload := lbl.remainder.advanceBits lbl.storedBits
  let rem0 : Nat := remaining - lbl.len
  if rem0 = 0 then
    -- Delete leaf.
    return (some payload, none, 0, #[cell])

  if cell.refs.size < 2 then
    throw .dictErr
  let nextPos : Nat := pos + lbl.len
  let swBit : Bool := key[nextPos]!
  let left0 := cell.refs[0]!
  let right0 := cell.refs[1]!
  let child0 := if swBit then right0 else left0
  let (oldVal?, childNew?, createdChild, loadedChild) ← dictDeleteAuxWithCells child0 key (nextPos + 1) (rem0 - 1)
  match oldVal? with
  | none =>
      -- Not found in subtree: unchanged.
      return (none, some cell, 0, #[cell] ++ loadedChild)
  | some oldVal =>
      match childNew? with
      | some childNew =>
          -- Both children present: rebuild fork with updated child.
          let newRefs : Array Cell := if swBit then #[left0, childNew] else #[childNew, right0]
          let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
          return (some oldVal, some newCell, createdChild + 1, #[cell] ++ loadedChild)
      | none =>
          -- One child removed: merge current edge with the surviving child.
          let survivorBit : Bool := !swBit
          let survivor : Cell := if swBit then left0 else right0
          let lbl2 ← parseDictLabel survivor (rem0 - 1)
          let childLabelBits := dictLabelBits lbl2
          let combinedLabelBits : BitString := dictLabelBits lbl ++ #[survivorBit] ++ childLabelBits
          let combinedLen : Nat := lbl.len + 1 + lbl2.len
          let enc : BitString := dictLabelEncode combinedLabelBits combinedLen remaining
          let payload2 := lbl2.remainder.advanceBits lbl2.storedBits
          let payloadCell2 : Cell := payload2.toCellRemaining
          let b0 ← builderStoreBitsChecked Builder.empty enc
          let b1 ← builderAppendCellChecked b0 payloadCell2
          return (some oldVal, some b1.finalize, createdChild + 1, #[cell] ++ loadedChild ++ #[survivor])

def dictDeleteWithCells (root : Option Cell) (key : BitString) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  match root with
  | none => return (none, none, 0, #[])
  | some cell =>
      dictDeleteAuxWithCells cell key 0 key.size

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

def dictSetBuilderWithCells (root : Option Cell) (key : BitString) (val : Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendBuilderChecked b val
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

def bitsXor (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! != b[i.1]!

def encodeTupleInstr (op : TupleInstr) : Except Excno BitString := do
  match op with
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
  | .unpackFirst n =>
      if n ≤ 15 then
        return natToBits (0x6f30 + n) 16
      else
        throw .rangeChk
  | .explode maxLen =>
      if maxLen ≤ 15 then
        return natToBits (0x6f40 + maxLen) 16
      else
        throw .rangeChk
  | .setIndex idx =>
      if idx ≤ 15 then
        return natToBits (0x6f50 + idx) 16
      else
        throw .rangeChk
  | .indexQ idx =>
      if idx ≤ 15 then
        return natToBits (0x6f60 + idx) 16
      else
        throw .rangeChk
  | .setIndexQ idx =>
      if idx ≤ 15 then
        return natToBits (0x6f70 + idx) 16
      else
        throw .rangeChk
  | .mktupleVar =>
      return natToBits 0x6f80 16
  | .indexVar =>
      return natToBits 0x6f81 16
  | .untupleVar =>
      return natToBits 0x6f82 16
  | .unpackFirstVar =>
      return natToBits 0x6f83 16
  | .explodeVar =>
      return natToBits 0x6f84 16
  | .setIndexVar =>
      return natToBits 0x6f85 16
  | .indexVarQ =>
      return natToBits 0x6f86 16
  | .setIndexVarQ =>
      return natToBits 0x6f87 16
  | .tlen =>
      return natToBits 0x6f88 16
  | .qtlen =>
      return natToBits 0x6f89 16
  | .isTuple =>
      return natToBits 0x6f8a 16
  | .last =>
      return natToBits 0x6f8b 16
  | .tpush =>
      return natToBits 0x6f8c 16
  | .tpop =>
      return natToBits 0x6f8d 16
  | .index2 i j =>
      if i < 4 ∧ j < 4 then
        return natToBits (0x6fb0 + ((i &&& 3) <<< 2) + (j &&& 3)) 16
      else
        throw .rangeChk
  | .index3 i j k =>
      if i < 4 ∧ j < 4 ∧ k < 4 then
        return natToBits (0x6fc0 + ((i &&& 3) <<< 4) + ((j &&& 3) <<< 2) + (k &&& 3)) 16
      else
        throw .rangeChk

def encodeCellInstr (op : CellInstr) : Except Excno BitString := do
  match op with
  | .subslice =>
      return natToBits 0xd734 16
  | .split quiet =>
      return natToBits (if quiet then 0xd737 else 0xd736) 16
  | .pldRefVar =>
      return natToBits 0xd748 16
  | .loadLeInt unsigned bytes prefetch quiet =>
      let lenBit : Nat ←
        if bytes = 4 then
          pure 0
        else if bytes = 8 then
          pure 2
        else
          throw .rangeChk
      let args4 : Nat :=
        (if unsigned then 1 else 0) +
          lenBit +
            (if prefetch then 4 else 0) +
              (if quiet then 8 else 0)
      return natToBits (0xd750 + args4) 16
  | .ldZeroes =>
      return natToBits 0xd760 16
  | .ldOnes =>
      return natToBits 0xd761 16
  | .ldSame =>
      return natToBits 0xd762 16
  | .sdepth =>
      return natToBits 0xd764 16
  | .clevel =>
      return natToBits 0xd766 16
  | .clevelMask =>
      return natToBits 0xd767 16
  | .chashI i =>
      if i ≤ 3 then
        return natToBits (0xd768 + i) 16
      else
        throw .rangeChk
  | .cdepthI i =>
      if i ≤ 3 then
        return natToBits (0xd76c + i) 16
      else
        throw .rangeChk
  | .chashIX =>
      return natToBits 0xd770 16
  | .cdepthIX =>
      return natToBits 0xd771 16
  | .schkBits quiet =>
      return natToBits (if quiet then 0xd745 else 0xd741) 16
  | .schkRefs quiet =>
      return natToBits (if quiet then 0xd746 else 0xd742) 16
  | .schkBitRefs quiet =>
      return natToBits (if quiet then 0xd747 else 0xd743) 16
  | .bdepth =>
      return natToBits 0xcf30 16
  | .brefs =>
      return natToBits 0xcf32 16
  | .bbitrefs =>
      return natToBits 0xcf33 16
  | .brembits =>
      return natToBits 0xcf35 16
  | .bremrefs =>
      return natToBits 0xcf36 16
  | .brembitrefs =>
      return natToBits 0xcf37 16
  | .bchkBitsImm bits quiet =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      return natToBits (if quiet then 0xcf3c else 0xcf38) 16 ++ natToBits (bits - 1) 8
  | .bchk needBits needRefs quiet =>
      let base : Nat :=
        if needBits && needRefs then
          if quiet then 0xcf3f else 0xcf3b
        else if needBits then
          if quiet then 0xcf3d else 0xcf39
        else if needRefs then
          if quiet then 0xcf3e else 0xcf3a
        else
          0
      if base = 0 then
        throw .invOpcode
      return natToBits base 16

def encodeCp0 (i : Instr) : Except Excno BitString := do
  match i with
  | .nop =>
      return natToBits 0x00 8
  | .pushInt .nan =>
      return natToBits 0x83ff 16
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
  | .pu2xc x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x546 <<< 12) + args
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
  | .blkPush x y =>
      if 1 ≤ x ∧ x ≤ 15 ∧ y ≤ 15 then
        let args8 : Nat := (x <<< 4) + y
        return natToBits (0x5f00 + args8) 16
      else
        throw .rangeChk
  | .rot =>
      return natToBits 0x58 8
  | .rotRev =>
      return natToBits 0x59 8
  | .twoSwap =>
      return natToBits 0x5a 8
  | .twoDup =>
      return natToBits 0x5c 8
  | .twoOver =>
      return natToBits 0x5d 8
  | .reverse x y =>
      if 2 ≤ x ∧ x ≤ 17 ∧ y ≤ 15 then
        let args : Nat := ((x - 2) <<< 4) + y
        return natToBits 0x5e 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .pick =>
      return natToBits 0x60 8
  | .roll =>
      return natToBits 0x61 8
  | .rollRev =>
      return natToBits 0x62 8
  | .blkSwapX =>
      return natToBits 0x63 8
  | .reverseX =>
      return natToBits 0x64 8
  | .dropX =>
      return natToBits 0x65 8
  | .tuck =>
      return natToBits 0x66 8
  | .xchgX =>
      return natToBits 0x67 8
  | .depth =>
      return natToBits 0x68 8
  | .chkDepth =>
      return natToBits 0x69 8
  | .onlyTopX =>
      return natToBits 0x6a 8
  | .onlyX =>
      return natToBits 0x6b 8
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
  | .endcst =>
      return natToBits 0xcd 8
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
  | .ldrefRtos =>
      return natToBits 0xd5 8
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
  | .stb rev quiet =>
      if !rev && !quiet then
        return natToBits 0xcf13 16
      else if rev && !quiet then
        return natToBits 0xcf17 16
      else if !rev && quiet then
        return natToBits 0xcf1b 16
      else
        return natToBits 0xcf1f 16
  | .stbRef rev quiet =>
      if !rev && !quiet then
        return natToBits 0xcf11 16
      else if rev && !quiet then
        return natToBits 0xcf15 16
      else if !rev && quiet then
        return natToBits 0xcf19 16
      else
        return natToBits 0xcf1d 16
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
  | .strefq =>
      return natToBits 0xcf18 16
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
  | .qnegate =>
      return natToBits 0xb7a3 16
  | .qpow2 =>
      return natToBits 0xb7ae 16
  | .inc =>
      return natToBits 0xa4 8
  | .qinc =>
      return natToBits 0xb7a4 16
  | .dec =>
      return natToBits 0xa5 8
  | .qdec =>
      return natToBits 0xb7a5 16
  | .add =>
      return natToBits 0xa0 8
  | .qadd =>
      return natToBits 0xb7a0 16
  | .addInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xa6 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .sub =>
      return natToBits 0xa1 8
  | .qsub =>
      return natToBits 0xb7a1 16
  | .qsubr =>
      return natToBits 0xb7a2 16
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
  | .qmul =>
      return natToBits 0xb7a8 16
  | .min =>
      return natToBits 0xb608 16
  | .max =>
      return natToBits 0xb609 16
  | .qmax =>
      return natToBits 0xb7b609 24
  | .minmax =>
      return natToBits 0xb60a 16
  | .qminmax =>
      return natToBits 0xb7b60a 24
  | .abs quiet =>
      if quiet then
        return natToBits 0xb7b60b 24
      else
        return natToBits 0xb60b 16
  | .bitsize =>
      return natToBits 0xb602 16
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
  | .mulDivMod d roundMode addMode quiet =>
      let roundEnc : Int := roundMode + 1
      if roundEnc < 0 ∨ roundEnc > 2 then
        throw .rangeChk
      if d > 3 then
        throw .rangeChk
      if addMode && d != 3 then
        throw .rangeChk
      let dEnc : Nat := if addMode then 0 else d
      if !addMode && dEnc = 0 then
        throw .rangeChk
      let args4 : Nat := (dEnc <<< 2) + roundEnc.toNat
      if quiet then
        let word24 : Nat := (0xb7a98 <<< 4) + args4
        return natToBits word24 24
      else
        return natToBits (0xa980 + args4) 16
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
  | .xor =>
      return natToBits 0xb2 8
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
  | .qcmp =>
      return natToBits 0xb7bf 16
  | .sbits =>
      return natToBits 0xd749 16
  | .srefs =>
      return natToBits 0xd74a 16
  | .sbitrefs =>
      return natToBits 0xd74b 16
  | .cdepth =>
      return natToBits 0xd765 16
  | .sempty =>
      return natToBits 0xc700 16
  | .sdempty =>
      return natToBits 0xc701 16
  | .srempty =>
      return natToBits 0xc702 16
  | .sdCntLead0 =>
      return natToBits 0xc710 16
  | .sdCntTrail0 =>
      return natToBits 0xc712 16
  | .sdEq =>
      return natToBits 0xc705 16
  | .sdPpfx =>
      return natToBits 0xc70a 16
  | .sdPfx =>
      return natToBits 0xc708 16
  | .sdPfxRev =>
      return natToBits 0xc709 16
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
  | .nullSwapIf =>
      return natToBits 0x6fa0 16
  | .nullSwapIfNot =>
      return natToBits 0x6fa1 16
  | .nullRotrIf =>
      return natToBits 0x6fa2 16
  | .nullRotrIfNot =>
      return natToBits 0x6fa3 16
  | .nullSwapIf2 =>
      return natToBits 0x6fa4 16
  | .nullSwapIfNot2 =>
      return natToBits 0x6fa5 16
  | .nullRotrIf2 =>
      return natToBits 0x6fa6 16
  | .nullRotrIfNot2 =>
      return natToBits 0x6fa7 16
  | .tupleOp op =>
      encodeTupleInstr op
  | .cellOp op =>
      encodeCellInstr op
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
  | .pushRef _ =>
      throw .invOpcode
  | .pushRefSlice _ =>
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
  | .prepareDict idx =>
      if idx > 0x3fff then
        throw .rangeChk
      let prefix10 : Nat := 0xf180 >>> 6
      let word24 : Nat := (prefix10 <<< 14) + (idx &&& 0x3fff)
      return natToBits word24 24
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
      else if idx ≤ 255 then
        return natToBits (0xf88100 + idx) 24
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
  | .globalId =>
      return natToBits 0xf835 16
  | .getGasFee =>
      return natToBits 0xf836 16
  | .getStorageFee =>
      return natToBits 0xf837 16
  | .getForwardFee =>
      return natToBits 0xf838 16
  | .getPrecompiledGas =>
      return natToBits 0xf839 16
  | .getOriginalFwdFee =>
      return natToBits 0xf83a 16
  | .getGasFeeSimple =>
      return natToBits 0xf83b 16
  | .getForwardFeeSimple =>
      return natToBits 0xf83c 16
  | .inMsgParam idx =>
      if idx ≤ 15 then
        return natToBits (0xf890 + idx) 16
      else
        throw .rangeChk
  | .ldGrams =>
      return natToBits 0xfa00 16
  | .stGrams =>
      return natToBits 0xfa02 16
  | .ldMsgAddr quiet =>
      return natToBits (if quiet then 0xfa41 else 0xfa40) 16
  | .rewriteStdAddr quiet =>
      return natToBits (if quiet then 0xfa45 else 0xfa44) 16
  | .hashExt hashId append rev =>
      if hashId > 255 then
        throw .rangeChk
      let args10 : Nat :=
        (hashId &&& 0xff) +
          (if rev then (1 <<< 8) else 0) +
            (if append then (1 <<< 9) else 0)
      let word24 : Nat := ((0xf904 >>> 2) <<< 10) + (args10 &&& 0x3ff)
      return natToBits word24 24
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
  | .rawReserveX =>
      return natToBits 0xfb03 16
  | .setCode =>
      return natToBits 0xfb04 16
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
  | .throwArg exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2c8 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwArgIf exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2d8 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwArgIfNot exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2e8 >>> 3
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
  | .dictGetNear args4 =>
      if args4 < 4 ∨ args4 > 15 then
        throw .rangeChk
      return natToBits (0xf470 + args4) 16
  | .dictGetMinMax args5 =>
      if args5 > 31 then
        throw .rangeChk
      -- Only the four fixed ranges used by TON: MIN, MAX, REMMIN, REMMAX.
      let ok :=
        (2 ≤ args5 ∧ args5 ≤ 7) ∨ (10 ≤ args5 ∧ args5 ≤ 15) ∨ (18 ≤ args5 ∧ args5 ≤ 23) ∨
          (26 ≤ args5 ∧ args5 ≤ 31)
      if !ok then
        throw .invOpcode
      return natToBits (0xf480 + args5) 16
  | .dictSet _ _ _ _ =>
      throw .invOpcode
  | .dictSetB _ _ _ =>
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
  return Cell.mkOrdinary bits #[]

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

def VmState.initial (code : Cell) (gasLimit : Int := 1_000_000) (gasMax : Int := GasLimits.infty)
    (gasCredit : Int := 0) : VmState :=
  { stack := #[]
    regs := { Regs.initial with c3 := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty }
    cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty
    cp := 0
    gas := GasLimits.ofLimits gasLimit gasMax gasCredit
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

def VmState.throwExceptionArg (st : VmState) (exc : Int) (arg : Value) : VmState :=
  let stack : Stack := #[arg, .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.ret (st : VmState) : VmState :=
  -- Mirrors C++ `VmState::ret()` as a jump to old `c0` after swapping `c0 := quit0`.
  let cont := st.regs.c0
  { st with regs := { st.regs with c0 := .quit 0 }, cc := cont }

def VmState.retAlt (st : VmState) : VmState :=
  -- Mirrors C++ `VmState::ret_alt()` as a jump to old `c1` after swapping `c1 := quit1`.
  let cont := st.regs.c1
  { st with regs := { st.regs with c1 := .quit 1 }, cc := cont }

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

  def VM.retAlt (passArgs : Int := -1) : VM Unit := do
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
    modify fun st => st.retAlt

def VmState.jumpTo (st : VmState) (k : Continuation) : VmState :=
  { st with cc := k }

def VmState.callToWithFrame (st : VmState) (frame : CallFrame) (k : Continuation) : VmState :=
  let oldC0 := st.regs.c0
  let retCont :=
    match st.cc with
    | .ordinary code _ _ _ =>
        -- Store the "old c0" in the return continuation's saved cregs, matching C++ `ControlData.save.c0`.
        let cregsRet : OrdCregs := { OrdCregs.empty with c0 := some oldC0 }
        .ordinary code (.quit 0) cregsRet OrdCdata.empty
    | _ => .quit 0
  { st with regs := { st.regs with c0 := retCont }, cc := k, callStack := st.callStack.push frame }

def VmState.callTo (st : VmState) (k : Continuation) : VmState :=
  st.callToWithFrame CallFrame.identity k

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

end TvmLean
