import Lean
import TvmLean.Model
import TvmLean.Validation.Canon.Value

namespace TvmLean

open Lean

structure CanonResult where
  exitRaw : Int
  gasUsed : Int
  c4Hash : String
  c5Hash : String
  stackTop : Array String
  deriving Repr, BEq

def canonCellHash (c : Cell) : String :=
  bytesHex (Cell.hashBytes c)

def canonStackTop (stack : Array Value) : Array String :=
  Array.ofFn (n := stack.size) fun i =>
    canonValue (stack[stack.size - 1 - i.1]!)

def CanonResult.ofLeanState
    (exitRaw : Int)
    (gasUsed : Int)
    (c4 : Cell)
    (c5 : Cell)
    (stack : Array Value) : CanonResult :=
  { exitRaw := exitRaw
    gasUsed := gasUsed
    c4Hash := canonCellHash c4
    c5Hash := canonCellHash c5
    stackTop := canonStackTop stack }

def CanonResult.ofOracleRaw
    (exitRaw : Int)
    (gasUsed : Int)
    (c4Hash : String)
    (c5Hash : String)
    (stackTop : Array String) : CanonResult :=
  { exitRaw, gasUsed, c4Hash, c5Hash, stackTop }

instance : ToJson CanonResult := ⟨fun r =>
  Json.mkObj
    [ ("exitRaw", ToJson.toJson r.exitRaw)
    , ("gasUsed", ToJson.toJson r.gasUsed)
    , ("c4Hash", Json.str r.c4Hash)
    , ("c5Hash", Json.str r.c5Hash)
    , ("stackTop", Json.arr (r.stackTop.map Json.str))
    ]⟩

end TvmLean
