import Std
import TvmLean.Model.Error.Excno
import TvmLean.Model.Value.IntVal

namespace TvmLean

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

def intUnsignedFitsBits (n : Int) (bits : Nat) : Bool :=
  if bits == 0 then
    n == 0
  else
    let hi : Int := intPow2 bits
    decide (0 ≤ n ∧ n < hi)

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
  -- Round to nearest for divisor `2^bits`, with ties towards +∞ (C++ BigInt round_mode = 0).
  if bits == 0 then
    n
  else
    let p : Int := intPow2 bits
    let qF := floorDivPow2 n bits
    let rF := n - qF * p
    if decide (rF * 2 ≥ p) then
      qF + 1
    else
      qF

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
  let p : Int := intPow2 bits
  let q := rshiftPow2Round n bits roundMode
  n - q * p

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
    -- roundMode = 0: nearest with ties towards +∞ (matches TON C++ BigInt::mod_div).
    let qF := floorDiv x y
    let rF := x - qF * y
    let q :=
      if (decide (y > 0) && decide (rF * 2 ≥ y)) || (decide (y < 0) && decide (rF * 2 ≤ y)) then
        qF + 1
      else
        qF
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

end TvmLean
