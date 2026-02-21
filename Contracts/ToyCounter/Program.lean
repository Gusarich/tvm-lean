import TvmLean.Model

namespace Contracts.ToyCounter.Program

open TvmLean

abbrev Counter32 := UInt32

def encodeCounter (n : Nat) : Cell :=
  (Builder.empty.storeBits (natToBits n 32)).finalize

def decodeCounter (c : Cell) : Except Excno Nat :=
  if c.bits.size = 32 ∧ c.refs.size = 0 then
    .ok (bitsToNat c.bits)
  else
    .error .cellUnd

def encodedInputValue (x : Counter32) : Nat :=
  bitsToNat (natToBits x.toNat 32)

def initialC4 (x : Counter32) : Cell :=
  encodeCounter x.toNat

def program : List Instr :=
  [ .pushCtr 4
  , .ctos
  , .ldu 32
  , .pop 0
  , .inc
  , .pushInt (.num 32)
  , .arithExt (.shrMod false false 2 (-1) false none)
  , .newc
  , .stu 32
  , .endc
  , .popCtr 4
  ]

def bytecode : Except Excno Cell :=
  assembleCp0 program

def decodeFuel : Nat := 64

end Contracts.ToyCounter.Program
