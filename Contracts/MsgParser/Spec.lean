import Contracts.MsgParser.Program

namespace Contracts.MsgParser.Spec

open TvmLean
open Contracts.MsgParser.Program

structure SpecState where
  msg : Cell
  deriving Repr

def initValid : SpecState :=
  { msg := msgAddrNoneCell }

def initInvalid : SpecState :=
  { msg := shortPrefixCell }

def runTagCheck (st : SpecState) : Option Int :=
  parsedTag? st.msg

def runTailCheck (st : SpecState) : Option Nat :=
  remainingBitsAfterParse? st.msg

def runGuard (st : SpecState) : Bool :=
  parseGuard st.msg

def PostValidTag (st : SpecState) : Prop :=
  runTagCheck st = some 0

def PostValidTail (st : SpecState) : Prop :=
  runTailCheck st = some tailBits.size

def PostInvalidGuard (st : SpecState) : Prop :=
  runGuard st = false

end Contracts.MsgParser.Spec
