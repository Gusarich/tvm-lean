import Tests.Harness.Registry
import TvmLean

open TvmLean
open Tests

namespace Tests.Harness.Gen.Cell

def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

def fullBuilder1023 : Builder :=
  Builder.empty.storeBits (Array.replicate 1023 false)

def maxUnsignedByBytes (bytes : Nat) : Int :=
  intPow2 (bytes * 8) - 1

def overflowUnsignedByBytes (bytes : Nat) : Int :=
  intPow2 (bytes * 8)

def encodeUnsignedVarIntBits (lenBits : Nat) (n : Int) : BitString :=
  let lenBytes : Nat := (natLenBits n.toNat + 7) / 8
  let payload := natToBits n.toNat (lenBytes * 8)
  natToBits lenBytes lenBits ++ payload

def encodeSignedVarIntBits (lenBits : Nat) (n : Int) : Except Excno BitString := do
  let lenBytes : Nat := (intSignedBitSizeTwos n + 7) / 8
  let payload ← intToBitsTwos n (lenBytes * 8)
  pure (natToBits lenBytes lenBits ++ payload)

def mkSliceFromBits (bs : BitString) : Slice :=
  Slice.ofCell (Builder.empty.storeBits bs).finalize

def build1023WithFixed
    (mkInstr : Nat → Instr)
    (x : IntVal := .num 0) : Array Instr :=
  #[
    .newc,
    .pushInt x, .xchg0 1, mkInstr 256,
    .pushInt x, .xchg0 1, mkInstr 256,
    .pushInt x, .xchg0 1, mkInstr 256,
    .pushInt x, .xchg0 1, mkInstr 255
  ]

def build1023WithFixedRev
    (mkInstr : Nat → Instr)
    (x : IntVal := .num 0) : Array Instr :=
  #[
    .newc,
    .pushInt x, mkInstr 256,
    .pushInt x, mkInstr 256,
    .pushInt x, mkInstr 256,
    .pushInt x, mkInstr 255
  ]

def build1023WithVar
    (instr : Instr)
    (x : IntVal := .num 0) : Array Instr :=
  #[
    .newc,
    .pushInt x, .xchg0 1, .pushInt (.num 256), instr,
    .pushInt x, .xchg0 1, .pushInt (.num 256), instr,
    .pushInt x, .xchg0 1, .pushInt (.num 256), instr,
    .pushInt x, .xchg0 1, .pushInt (.num 255), instr
  ]

def build1023WithVarRev
    (instr : Instr)
    (x : IntVal := .num 0) : Array Instr :=
  #[
    .newc,
    .pushInt x, .pushInt (.num 256), instr,
    .pushInt x, .pushInt (.num 256), instr,
    .pushInt x, .pushInt (.num 256), instr,
    .pushInt x, .pushInt (.num 255), instr
  ]

def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx => ((idx.1 + phase) % 2 = 1)

def mkSliceWithBitsRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

def refLeafA : Cell := Cell.mkOrdinary (natToBits 5 3) #[]
def refLeafB : Cell := Cell.mkOrdinary (natToBits 9 4) #[]
def refLeafC : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

def tailBits3 : BitString := natToBits 5 3
def tailBits5 : BitString := natToBits 21 5
def tailBits7 : BitString := natToBits 93 7
def tailBits11 : BitString := natToBits 1337 11
def tailBits13 : BitString := natToBits 4242 13

def randBitString (count : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

def bytesToBitsBE (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok ls, .ok rs => ls == rs
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  Id.run do
    let mut out : Array Instr := #[]
    let mut rem := bits
    while rem > 0 do
      let chunk : Nat := Nat.min 256 rem
      out := out ++ #[.pushInt x, .xchg0 1, .stu chunk]
      rem := rem - chunk
    return out

def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

end Tests.Harness.Gen.Cell
