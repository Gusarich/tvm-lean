import Lean
import TvmLean.Validation.Canon.Result

namespace TvmLean

open Lean

inductive OracleDiffField where
  | exitRaw
  | gasUsed
  | c4Hash
  | c5Hash
  | stackDepth
  | stackItem (idx : Nat)
  deriving Repr, BEq

structure OracleMismatch where
  field : OracleDiffField
  lean : String
  oracle : String
  deriving Repr, BEq

structure OracleComparison where
  lean : CanonResult
  oracle : CanonResult
  mismatch? : Option OracleMismatch := none
  deriving Repr

def OracleComparison.ok (cmp : OracleComparison) : Bool :=
  cmp.mismatch?.isNone

def OracleMismatch.message (m : OracleMismatch) : String :=
  match m.field with
  | .exitRaw => s!"EXIT mismatch: lean={m.lean} oracle={m.oracle}"
  | .gasUsed => s!"GAS mismatch: lean={m.lean} oracle={m.oracle}"
  | .c4Hash => s!"C4 mismatch: lean={m.lean} oracle={m.oracle}"
  | .c5Hash => s!"C5 mismatch: lean={m.lean} oracle={m.oracle}"
  | .stackDepth => s!"STACK depth mismatch: lean={m.lean} oracle={m.oracle}"
  | .stackItem idx => s!"STACK mismatch at idx={idx}: lean='{m.lean}' oracle='{m.oracle}'"

def compareCanonResults (lean oracle : CanonResult) : OracleComparison :=
  let base : OracleComparison := { lean, oracle, mismatch? := none }
  if lean.exitRaw != oracle.exitRaw then
    { base with mismatch? := some { field := .exitRaw, lean := toString lean.exitRaw, oracle := toString oracle.exitRaw } }
  else if lean.gasUsed != oracle.gasUsed then
    { base with mismatch? := some { field := .gasUsed, lean := toString lean.gasUsed, oracle := toString oracle.gasUsed } }
  else if lean.c4Hash != oracle.c4Hash then
    { base with mismatch? := some { field := .c4Hash, lean := lean.c4Hash, oracle := oracle.c4Hash } }
  else if lean.c5Hash != oracle.c5Hash then
    { base with mismatch? := some { field := .c5Hash, lean := lean.c5Hash, oracle := oracle.c5Hash } }
  else if lean.stackTop.size != oracle.stackTop.size then
    { base with
        mismatch? := some
          { field := .stackDepth
            lean := toString lean.stackTop.size
            oracle := toString oracle.stackTop.size } }
  else
    Id.run do
      for i in [0:lean.stackTop.size] do
        let l := lean.stackTop[i]!
        let r := oracle.stackTop[i]!
        if l != r then
          return { base with mismatch? := some { field := .stackItem i, lean := l, oracle := r } }
      base

instance : ToJson OracleDiffField := ⟨fun f =>
  match f with
  | .exitRaw => Json.str "exitRaw"
  | .gasUsed => Json.str "gasUsed"
  | .c4Hash => Json.str "c4Hash"
  | .c5Hash => Json.str "c5Hash"
  | .stackDepth => Json.str "stackDepth"
  | .stackItem idx => Json.str s!"stack[{idx}]"⟩

instance : ToJson OracleMismatch := ⟨fun m =>
  Json.mkObj
    [ ("field", ToJson.toJson m.field)
    , ("lean", Json.str m.lean)
    , ("oracle", Json.str m.oracle)
    , ("message", Json.str m.message)
    ]⟩

instance : ToJson OracleComparison := ⟨fun cmp =>
  Json.mkObj
    [ ("ok", ToJson.toJson cmp.ok)
    , ("lean", ToJson.toJson cmp.lean)
    , ("oracle", ToJson.toJson cmp.oracle)
    , ("mismatch",
        match cmp.mismatch? with
        | some m => ToJson.toJson m
        | none => Json.null)
    ]⟩

end TvmLean
