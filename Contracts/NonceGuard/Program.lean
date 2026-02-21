import TvmLean.Model.Cell.Primitives

namespace Contracts.NonceGuard.Program

open TvmLean

def nonceKeyBits : Nat :=
  32

def keyOfNonce (nonce : Nat) : BitString :=
  natToBits nonce nonceKeyBits

def nonceMarker : Cell :=
  Cell.empty

def lookupNonce (root : Option Cell) (nonce : Nat) : Except Excno (Option Slice) :=
  dictLookup root (keyOfNonce nonce)

def addNonce (root : Option Cell) (nonce : Nat) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) :=
  dictSetRefWithCells root (keyOfNonce nonce) nonceMarker .add

end Contracts.NonceGuard.Program
