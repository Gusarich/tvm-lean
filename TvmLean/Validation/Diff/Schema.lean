import Lean
import TvmLean.Model
import TvmLean.Boc

namespace TvmLean

open Lean

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (10 + (c.toNat - 'A'.toNat))
  else
    none

def hexDecode (hex : String) : Except String ByteArray := do
  let s := hex.trim
  let chars := s.data.toArray
  if chars.size % 2 ≠ 0 then
    throw s!"hex length must be even, got {chars.size}"
  let mut out : Array UInt8 := #[]
  for i in [0:(chars.size / 2)] do
    let a := chars[2 * i]!
    let b := chars[2 * i + 1]!
    let hi ←
      match hexVal a with
      | some v => pure v
      | none => throw s!"invalid hex digit '{a}'"
    let lo ←
      match hexVal b with
      | some v => pure v
      | none => throw s!"invalid hex digit '{b}'"
    out := out.push (UInt8.ofNat (hi * 16 + lo))
  return ByteArray.mk out

def base64Val (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then
    some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'z' then
    some (26 + (c.toNat - 'a'.toNat))
  else if '0' ≤ c ∧ c ≤ '9' then
    some (52 + (c.toNat - '0'.toNat))
  else if c = '+' then
    some 62
  else if c = '/' then
    some 63
  else
    none

def base64Decode (input : String) : Except String ByteArray := do
  let chars := (input.trim.data.filter (fun c => !c.isWhitespace)).toArray
  if chars.size % 4 ≠ 0 then
    throw s!"base64 length must be a multiple of 4, got {chars.size}"

  let groups := chars.size / 4
  let mut out : Array UInt8 := #[]

  for gi in [0:groups] do
    let i := gi * 4
    let c0 := chars[i]!
    let c1 := chars[i + 1]!
    let c2 := chars[i + 2]!
    let c3 := chars[i + 3]!

    let v0 ←
      match base64Val c0 with
      | some v => pure v
      | none => throw s!"invalid base64 char '{c0}'"
    let v1 ←
      match base64Val c1 with
      | some v => pure v
      | none => throw s!"invalid base64 char '{c1}'"

    let pad2 := c2 = '='
    let pad3 := c3 = '='
    if pad2 && !pad3 then
      throw "invalid base64 padding"
    if (pad2 || pad3) && gi ≠ groups - 1 then
      throw "invalid base64 padding (must be in the last block)"

    let v2 ←
      if pad2 then
        pure 0
      else
        match base64Val c2 with
        | some v => pure v
        | none => throw s!"invalid base64 char '{c2}'"
    let v3 ←
      if pad3 then
        pure 0
      else
        match base64Val c3 with
        | some v => pure v
        | none => throw s!"invalid base64 char '{c3}'"

    let b0 : Nat := (v0 <<< 2) ||| (v1 >>> 4)
    out := out.push (UInt8.ofNat b0)
    if !pad2 then
      let b1 : Nat := ((v1 &&& 0x0f) <<< 4) ||| (v2 >>> 2)
      out := out.push (UInt8.ofNat b1)
    if !pad3 then
      let b2 : Nat := ((v2 &&& 0x03) <<< 6) ||| v3
      out := out.push (UInt8.ofNat b2)

  return ByteArray.mk out

def decodeBytes (s : String) : Except String ByteArray := do
  if s.startsWith "hex:" then
    hexDecode (s.drop 4)
  else if s.startsWith "base64:" then
    base64Decode (s.drop 7)
  else
    base64Decode s

instance [FromJson α] : FromJson (Array α) where
  fromJson? j := do
    let xs ← FromJson.fromJson? (α := List α) j
    return xs.toArray

inductive ExpectedVal : Type
  | null
  | int (n : Int)
  | nan
  | cell (boc : String)
  | slice (boc : String)
  | builder (boc : String)
  | tuple (items : Array ExpectedVal)
  deriving Repr

partial def expectedValFromJson? (j : Json) : Except String ExpectedVal := do
  let ty ← j.getObjValAs? String "type"
  match ty with
  | "null" => return .null
  | "nan" => return .nan
  | "int" =>
      let nStr? := j.getObjValAs? String "value"
      let n : Int ←
        match nStr? with
        | .ok s =>
            match s.toInt? with
            | some n => pure n
            | none => throw s!"invalid int value '{s}'"
        | .error _ =>
            j.getObjValAs? Int "value"
      return .int n
  | "cell" =>
      return .cell (← j.getObjValAs? String "boc")
  | "slice" =>
      return .slice (← j.getObjValAs? String "boc")
  | "builder" =>
      return .builder (← j.getObjValAs? String "boc")
  | "tuple" =>
      let itemsJ ← j.getObjVal? "items"
      match itemsJ with
      | .arr items =>
          let mut out : Array ExpectedVal := #[]
          for it in items do
            out := out.push (← expectedValFromJson? it)
          return .tuple out
      | _ =>
          throw "ExpectedVal.tuple.items must be a JSON array"
  | other =>
      throw s!"unknown ExpectedVal type '{other}'"

instance : FromJson ExpectedVal where
  fromJson? := expectedValFromJson?

def decodeCellBoc (s : String) : Except String Cell := do
  let bytes ← decodeBytes s
  match stdBocDeserialize bytes with
  | .ok c => pure c
  | .error e => throw (toString e)

partial def ExpectedVal.toValue : ExpectedVal → Except String Value
  | .null => .ok .null
  | .nan => .ok (.int .nan)
  | .int n => .ok (.int (.num n))
  | .cell boc => do
      let c ← decodeCellBoc boc
      return .cell c
  | .slice boc => do
      let c ← decodeCellBoc boc
      return .slice (Slice.ofCell c)
  | .builder boc => do
      let c ← decodeCellBoc boc
      return .builder { bits := c.bits, refs := c.refs }
  | .tuple items => do
      let mut out : Array Value := #[]
      for it in items do
        let v ← it.toValue
        out := out.push v
      return .tuple out

structure Expected where
  exit_code : Int
  gas_used : Option Int := none
  gas_limit : Option Int := none
  gas_max : Option Int := none
  gas_credit : Option Int := none
  c4_boc : Option String := none
  c5_boc : Option String := none
  c7 : Option ExpectedVal := none
  deriving Repr

instance : FromJson Expected where
  fromJson? j := do
    let exit_code ← j.getObjValAs? Int "exit_code"
    let gas_used :=
      match j.getObjValAs? Int "gas_used" with
      | .ok v => some v
      | .error _ =>
          match j.getObjValAs? String "gas_used" with
          | .ok s =>
              match s.toInt? with
              | some n => some n
              | none => none
          | .error _ => none
    let gas_limit :=
      match j.getObjValAs? Int "gas_limit" with
      | .ok v => some v
      | .error _ =>
          match j.getObjValAs? String "gas_limit" with
          | .ok s => s.toInt?
          | .error _ => none
    let gas_max :=
      match j.getObjValAs? Int "gas_max" with
      | .ok v => some v
      | .error _ =>
          match j.getObjValAs? String "gas_max" with
          | .ok s => s.toInt?
          | .error _ => none
    let gas_credit :=
      match j.getObjValAs? Int "gas_credit" with
      | .ok v => some v
      | .error _ =>
          match j.getObjValAs? String "gas_credit" with
          | .ok s => s.toInt?
          | .error _ => none
    let c4_boc :=
      match j.getObjValAs? String "c4_boc" with
      | .ok s => some s
      | .error _ => none
    let c5_boc :=
      match j.getObjValAs? String "c5_boc" with
      | .ok s => some s
      | .error _ => none
    let c7 :=
      match j.getObjValAs? ExpectedVal "c7" with
      | .ok v => some v
      | .error _ => none
    return { exit_code, gas_used, gas_limit, gas_max, gas_credit, c4_boc, c5_boc, c7 }

structure StackInit where
  balance_grams : Int
  msg_balance_grams : Int
  now : Int := 0
  lt : Int := 0
  rand_seed : Int := 0
  storage_fees : Int := 0
  due_payment : Int := 0
  in_msg_boc : String
  in_msg_body_boc : String
  in_msg_extern : Bool
  -- Full blockchain config cell (HashmapE 32 -> Cell), used by CONFIGROOT (c7 params[9]) and for accurate c7 init.
  config_root_boc : Option String := none
  -- Selected ConfigParams used by UNPACKEDCONFIGTUPLE (c7 params[14]).
  config_storage_prices_boc : Option String := none -- ConfigParam 18 (StoragePrices dict)
  config_global_id_boc : Option String := none -- ConfigParam 19 (Global ID)
  config_mc_gas_prices_boc : Option String := none -- ConfigParam 20 (GasPrices for masterchain)
  config_gas_prices_boc : Option String := none -- ConfigParam 21 (GasPrices for basechain)
  -- ConfigParam 24 / 25 (MsgForwardPrices), needed for GETORIGINALFWDFEE and related opcodes.
  config_mc_fwd_prices_boc : Option String := none
  config_fwd_prices_boc : Option String := none
  config_size_limits_boc : Option String := none -- ConfigParam 43 (SizeLimits)
  -- ConfigParam 45 (PrecompiledContractsConfig), needed to populate GETPRECOMPILEDGAS and to detect/skip precompiled contracts in diff tests.
  config_precompiled_contracts_boc : Option String := none
  deriving Repr

instance : FromJson StackInit where
  fromJson? j := do
    let balanceStr ← j.getObjValAs? String "balance_grams"
    let msgBalanceStr ← j.getObjValAs? String "msg_balance_grams"
    let now : Int ←
      match j.getObjValAs? String "now" with
      | .ok s =>
          match s.toInt? with
          | some n => pure n
          | none => throw s!"invalid now '{s}'"
      | .error _ =>
          match j.getObjValAs? Int "now" with
          | .ok n => pure n
          | .error _ => pure 0
    let lt : Int ←
      match j.getObjValAs? String "lt" with
      | .ok s =>
          match s.toInt? with
          | some n => pure n
          | none => throw s!"invalid lt '{s}'"
      | .error _ =>
          match j.getObjValAs? Int "lt" with
          | .ok n => pure n
          | .error _ => pure 0
    let rand_seed : Int ←
      match j.getObjValAs? String "rand_seed" with
      | .ok s =>
          match s.toInt? with
          | some n => pure n
          | none => throw s!"invalid rand_seed '{s}'"
      | .error _ =>
          match j.getObjValAs? Int "rand_seed" with
          | .ok n => pure n
          | .error _ => pure 0
    let storage_fees : Int ←
      match j.getObjValAs? String "storage_fees" with
      | .ok s =>
          match s.toInt? with
          | some n => pure n
          | none => throw s!"invalid storage_fees '{s}'"
      | .error _ =>
          match j.getObjValAs? Int "storage_fees" with
          | .ok n => pure n
          | .error _ => pure 0
    let due_payment : Int ←
      match j.getObjValAs? String "due_payment" with
      | .ok s =>
          match s.toInt? with
          | some n => pure n
          | none => throw s!"invalid due_payment '{s}'"
      | .error _ =>
          match j.getObjValAs? Int "due_payment" with
          | .ok n => pure n
          | .error _ => pure 0
    let in_msg_boc ← j.getObjValAs? String "in_msg_boc"
    let in_msg_body_boc ← j.getObjValAs? String "in_msg_body_boc"
    let in_msg_extern ← j.getObjValAs? Bool "in_msg_extern"
    let config_root_boc :=
      match j.getObjValAs? String "config_root_boc" with
      | .ok s => some s
      | .error _ => none
    let config_storage_prices_boc :=
      match j.getObjValAs? String "config_storage_prices_boc" with
      | .ok s => some s
      | .error _ => none
    let config_global_id_boc :=
      match j.getObjValAs? String "config_global_id_boc" with
      | .ok s => some s
      | .error _ => none
    let config_mc_gas_prices_boc :=
      match j.getObjValAs? String "config_mc_gas_prices_boc" with
      | .ok s => some s
      | .error _ => none
    let config_gas_prices_boc :=
      match j.getObjValAs? String "config_gas_prices_boc" with
      | .ok s => some s
      | .error _ => none
    let config_mc_fwd_prices_boc :=
      match j.getObjValAs? String "config_mc_fwd_prices_boc" with
      | .ok s => some s
      | .error _ => none
    let config_fwd_prices_boc :=
      match j.getObjValAs? String "config_fwd_prices_boc" with
      | .ok s => some s
      | .error _ => none
    let config_size_limits_boc :=
      match j.getObjValAs? String "config_size_limits_boc" with
      | .ok s => some s
      | .error _ => none
    let config_precompiled_contracts_boc :=
      match j.getObjValAs? String "config_precompiled_contracts_boc" with
      | .ok s => some s
      | .error _ => none
    let balance_grams ←
      match balanceStr.toInt? with
      | some n => pure n
      | none => throw s!"invalid balance_grams '{balanceStr}'"
    let msg_balance_grams ←
      match msgBalanceStr.toInt? with
      | some n => pure n
      | none => throw s!"invalid msg_balance_grams '{msgBalanceStr}'"
    return {
      balance_grams,
      msg_balance_grams,
      now,
      lt,
      rand_seed,
      storage_fees,
      due_payment,
      in_msg_boc,
      in_msg_body_boc,
      in_msg_extern,
      config_root_boc,
      config_storage_prices_boc,
      config_global_id_boc,
      config_mc_gas_prices_boc,
      config_gas_prices_boc,
      config_mc_fwd_prices_boc,
      config_fwd_prices_boc,
      config_size_limits_boc,
      config_precompiled_contracts_boc
    }

structure TestCase where
  tx_hash : String
  code_boc : String
  mycode_boc? : Option String := none
  data_boc : String
  stack_init : StackInit
  expected : Expected
  deriving Repr

instance : FromJson TestCase where
  fromJson? j := do
    let tx_hash ← j.getObjValAs? String "tx_hash"
    let code_boc ← j.getObjValAs? String "code_boc"
    let mycode_boc? :=
      match j.getObjValAs? String "mycode_boc" with
      | .ok s => some s
      | .error _ => none
    let data_boc ← j.getObjValAs? String "data_boc"
    let stack_init ← j.getObjValAs? StackInit "stack_init"
    let expected ← j.getObjValAs? Expected "expected"
    return { tx_hash, code_boc, mycode_boc?, data_boc, stack_init, expected }


end TvmLean
