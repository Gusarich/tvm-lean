import TvmLean.Model.Cell.Primitives

namespace Contracts.MsgParser.Program

open TvmLean

def tailBits : BitString :=
  #[true, false, true]

def msgAddrNoneCell : Cell :=
  Cell.mkOrdinary (natToBits 0 2 ++ tailBits) #[]

def shortPrefixCell : Cell :=
  Cell.mkOrdinary #[true] #[]

def parseFromCell (cell : Cell) : Except Excno (Array Value × Slice) :=
  (Slice.ofCell cell).parseMessageAddr

def parsedTag? (cell : Cell) : Option Int :=
  match parseFromCell cell with
  | .error _ => none
  | .ok (values, _) =>
      match values[0]? with
      | some (Value.int (IntVal.num tag)) => some tag
      | _ => none

def remainingBitsAfterParse? (cell : Cell) : Option Nat :=
  match parseFromCell cell with
  | .error _ => none
  | .ok (_, rest) => some rest.bitsRemaining

def parseGuard (cell : Cell) : Bool :=
  match parseFromCell cell with
  | .ok _ => true
  | .error _ => false

end Contracts.MsgParser.Program
