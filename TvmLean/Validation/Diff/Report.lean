import Lean
import TvmLean.Semantics

namespace TvmLean

open Lean

inductive DiffStatus
  | pass
  | fail
  | skip
  | error
  deriving DecidableEq, Repr

instance : ToString DiffStatus := ⟨fun
  | .pass => "PASS"
  | .fail => "FAIL"
  | .skip => "SKIP"
  | .error => "ERROR"⟩

instance : ToJson DiffStatus := ⟨fun s => Json.str (toString s)⟩

instance : ToJson TraceEntry := ⟨fun t =>
  Json.mkObj
    [ ("step", ToJson.toJson t.step)
    , ("event", Json.str t.event)
    , ("cp", ToJson.toJson t.cp)
    , ("cc_before", Json.str t.cc_before)
    , ("cc_after", Json.str t.cc_after)
    , ("gas_before", ToJson.toJson t.gas_before)
    , ("gas_after", ToJson.toJson t.gas_after)
    , ("stack_before", Json.str t.stack_before)
    , ("stack_after", Json.str t.stack_after)
    ]⟩

structure TestResult where
  tx_hash : String
  status : DiffStatus
  expected_exit_code : Int
  actual_exit_code : Option Int := none
  expected_gas_used : Option Int := none
  actual_gas_used : Option Int := none
  error : Option String := none
  trace : Option (Array TraceEntry) := none
  trace_truncated : Option Bool := none
  deriving Repr

instance : ToJson TestResult := ⟨fun r =>
  Id.run do
    let mut obj : Array (String × Json) := #[
      ("tx_hash", Json.str r.tx_hash),
      ("status", ToJson.toJson r.status),
      ("expected_exit_code", ToJson.toJson r.expected_exit_code),
      ("expected_gas_used", ToJson.toJson r.expected_gas_used)
    ]
    obj :=
      match r.actual_exit_code with
      | some v => obj.push ("actual_exit_code", ToJson.toJson v)
      | none => obj
    obj :=
      match r.actual_gas_used with
      | some v => obj.push ("actual_gas_used", ToJson.toJson v)
      | none => obj
    obj :=
      match r.error with
      | some e => obj.push ("error", Json.str e)
      | none => obj
    obj :=
      match r.trace with
      | some t => obj.push ("trace", Json.arr (t.map ToJson.toJson))
      | none => obj
    obj :=
      match r.trace_truncated with
      | some t => obj.push ("trace_truncated", ToJson.toJson t)
      | none => obj
    return Json.mkObj obj.toList⟩


end TvmLean
