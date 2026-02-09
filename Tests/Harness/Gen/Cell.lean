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

end Tests.Harness.Gen.Cell
