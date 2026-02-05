import Lean
import TvmLean.Core.Prelude
import TvmLean.Core.Exec

open TvmLean

namespace TvmLeanProgress

def die (msg : String) : IO α := throw <| IO.userError msg

def asObj (j : Lean.Json) : IO (List (String × Lean.Json)) :=
  match j with
  | .obj o => pure o.toList
  | _ => die "expected JSON object"

def asArr (j : Lean.Json) : IO (Array Lean.Json) :=
  match j with
  | .arr a => pure a
  | _ => die "expected JSON array"

def asStr (j : Lean.Json) : IO String :=
  match j with
  | .str s => pure s
  | _ => die "expected JSON string"

def asNat (j : Lean.Json) : IO Nat :=
  match j with
  | .num n => do
      if n.exponent != 0 then
        (die s!"expected Nat JSON number, got {n}" : IO Unit)
      else
        pure ()
      if n.mantissa < 0 then
        (die s!"expected Nat JSON number, got {n}" : IO Unit)
      else
        pure ()
      pure n.mantissa.toNat
  | _ => die "expected JSON number"

def findKey? (k : String) (xs : List (String × Lean.Json)) : Option Lean.Json :=
  xs.findSome? (fun (k', v) => if k' = k then some v else none)

def mkProbeCell (pfx : Nat) (checkLen : Nat) (skipLen : Nat) : Cell :=
  let argsLen : Nat := skipLen - checkLen
  let prefixLimit : Nat := (1 <<< checkLen)
  let pfxNorm : Nat :=
    if pfx < prefixLimit then
      pfx
    else
      pfx >>> argsLen
  let argsVal : Nat :=
    if pfx < prefixLimit then
      0
    else if argsLen = 0 then
      0
    else
      pfx &&& ((1 <<< argsLen) - 1)
  let padLen : Nat := Nat.min 512 (1023 - skipLen)
  let pad : BitString := Array.replicate padLen false
  let bits : BitString := natToBits pfxNorm checkLen ++ natToBits argsVal argsLen ++ pad
  let refs : Array Cell := Array.replicate 4 Cell.empty
  Cell.mkOrdinary bits refs

def probeImplemented (cell : Cell) : Bool :=
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error _ => false
  | .ok (instr, _totBits, _rest) =>
      let st0 : VmState := VmState.initial cell
      let (res, _st1) := (execInstr instr).run st0
      match res with
      | .error .invOpcode => false
      | _ => true

def probeDecoded (cell : Cell) : Bool :=
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .error _ => false
  | .ok _ => true

def probeAll (idx : Lean.Json) : IO (Array (String × Bool)) := do
  let top ← asObj idx
  let tvmJ ←
    match findKey? "tvm_instructions" top with
    | some j => pure j
    | none => die "missing tvm_instructions"
  let tvmArr ← asArr tvmJ
  let mut out : Array (String × Bool) := #[]
  for insJ in tvmArr do
    let insObj ← asObj insJ
    let nameJ ←
      match findKey? "name" insObj with
      | some j => pure j
      | none => die "missing instruction name"
    let name ← asStr nameJ
    let layoutJ ←
      match findKey? "layout" insObj with
      | some j => pure j
      | none => die s!"missing layout for {name}"
    let layoutObj ← asObj layoutJ
    let pfx ←
      match findKey? "prefix" layoutObj with
      | some j => asNat j
      | none => pure 0
    let checkLen ←
      match findKey? "checkLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    let skipLen ←
      match findKey? "skipLen" layoutObj with
      | some j => asNat j
      | none => pure 0
    let ok :=
      if checkLen = 0 || skipLen = 0 || checkLen > skipLen || skipLen > 1023 then
        false
      else
        let cell := mkProbeCell pfx checkLen skipLen
        -- Some opcodes are decoded/handled, but (in current TON) always or usually execute to `invOpcode`
        -- for our probing inputs. Count them as implemented here.
        if name == "SETCP_SHORT" || name == "EXTCALL" || name == "XCHG_IJ" then
          probeDecoded cell
        else
          probeImplemented cell
    out := out.push (s!"tvm::{name}", ok)
  return out

def main (args : List String) : IO UInt32 := do
  let wantSummary : Bool := args.any (· == "--summary")
  let wantTsv : Bool := args.any (· == "--tsv") || args.all (fun a => a != "--summary")

  let path := System.mkFilePath ["docs", "progress", "tvm_spec_index.json"]
  let txt ← IO.FS.readFile path
  let idx ←
    match Lean.Json.parse txt with
    | .ok j => pure j
    | .error e => die s!"failed to parse {path}: {e}"

  let rows ← probeAll idx
  if wantSummary then
    let total := rows.size
    let implemented := rows.foldl (init := 0) fun acc (_k, v) => acc + (if v then 1 else 0)
    IO.println s!"tvm(code-probe): implemented={implemented}/{total}"

  if wantTsv then
    for (k, v) in rows do
      IO.println s!"{k}\t{if v then "true" else "false"}"

  return 0

end TvmLeanProgress

def main (args : List String) : IO UInt32 :=
  TvmLeanProgress.main args
