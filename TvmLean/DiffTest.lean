import Lean
import TvmLean.Core
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
    return { exit_code, gas_used, c4_boc, c5_boc, c7 }

structure StackInit where
  balance_grams : Int
  msg_balance_grams : Int
  in_msg_boc : String
  in_msg_body_boc : String
  in_msg_extern : Bool
  deriving Repr

instance : FromJson StackInit where
  fromJson? j := do
    let balanceStr ← j.getObjValAs? String "balance_grams"
    let msgBalanceStr ← j.getObjValAs? String "msg_balance_grams"
    let in_msg_boc ← j.getObjValAs? String "in_msg_boc"
    let in_msg_body_boc ← j.getObjValAs? String "in_msg_body_boc"
    let in_msg_extern ← j.getObjValAs? Bool "in_msg_extern"
    let balance_grams ←
      match balanceStr.toInt? with
      | some n => pure n
      | none => throw s!"invalid balance_grams '{balanceStr}'"
    let msg_balance_grams ←
      match msgBalanceStr.toInt? with
      | some n => pure n
      | none => throw s!"invalid msg_balance_grams '{msgBalanceStr}'"
    return { balance_grams, msg_balance_grams, in_msg_boc, in_msg_body_boc, in_msg_extern }

structure TestCase where
  tx_hash : String
  code_boc : String
  data_boc : String
  stack_init : StackInit
  expected : Expected
  deriving Repr

instance : FromJson TestCase where
  fromJson? j := do
    let tx_hash ← j.getObjValAs? String "tx_hash"
    let code_boc ← j.getObjValAs? String "code_boc"
    let data_boc ← j.getObjValAs? String "data_boc"
    let stack_init ← j.getObjValAs? StackInit "stack_init"
    let expected ← j.getObjValAs? Expected "expected"
    return { tx_hash, code_boc, data_boc, stack_init, expected }

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

structure RunConfig where
  fuel : Nat := 1_000_000
  gasLimit : Int := 1_000_000
  skipUnsupported : Bool := false
  traceFailures : Bool := false
  traceAll : Bool := false
  traceMax : Nat := 200
  deriving Repr

def loadTestCase (path : System.FilePath) : IO TestCase := do
  let s ← IO.FS.readFile path
  let j ←
    match Json.parse s with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"{path}: JSON parse error: {e}")
  match (FromJson.fromJson? (α := TestCase) j) with
  | .ok tc => pure tc
  | .error e => throw (IO.userError s!"{path}: JSON schema error: {e}")

def buildInitStack (si : StackInit) : Except String Stack := do
  let inMsgBytes ← decodeBytes si.in_msg_boc
  let inMsgCell ←
    match stdBocDeserialize inMsgBytes with
    | .ok c => pure c
    | .error e => throw s!"in_msg_boc: {e}"
  let bodyBytes ← decodeBytes si.in_msg_body_boc
  let bodyCell ←
    match stdBocDeserialize bodyBytes with
    | .ok c => pure c
    | .error e => throw s!"in_msg_body_boc: {e}"
  let flag : Int := if si.in_msg_extern then -1 else 0
  return #[
    .int (.num si.balance_grams),
    .int (.num si.msg_balance_grams),
    .cell inMsgCell,
    .slice (Slice.ofCell bodyCell),
    .int (.num flag)
  ]

def runTestCase (cfg : RunConfig) (tc : TestCase) : IO TestResult := do
  let mkErr (msg : String) : TestResult :=
    { tx_hash := tc.tx_hash
      status := .error
      expected_exit_code := tc.expected.exit_code
      expected_gas_used := tc.expected.gas_used
      error := some msg }

  match decodeBytes tc.code_boc with
  | .error e => return mkErr s!"code_boc decode: {e}"
  | .ok codeBytes =>
      match decodeBytes tc.data_boc with
      | .error e => return mkErr s!"data_boc decode: {e}"
      | .ok dataBytes =>
          match stdBocDeserialize codeBytes with
          | .error e => return mkErr s!"code_boc parse: {e}"
          | .ok codeCell =>
              match stdBocDeserialize dataBytes with
              | .error e => return mkErr s!"data_boc parse: {e}"
              | .ok dataCell =>
                  match buildInitStack tc.stack_init with
                  | .error e => return mkErr s!"stack_init: {e}"
                  | .ok initStack =>
                      let st0 : VmState :=
                        { (VmState.initial codeCell cfg.gasLimit) with
                          stack := initStack
                          regs := { (Regs.initial) with c4 := dataCell } }

                      let mkBase (exitCode : Int) (stF : VmState) : TestResult :=
                        -- `VmState.run*` returns bitwise-complemented exit codes (like C++ `vm.run()`).
                        -- Blockchain `compute_exit_code` is the uncomplemented one (like C++ `cp.exit_code = ~vm.run()`).
                        let actualExit : Int := ~~~ exitCode
                        let gasUsed : Int := stF.gas.gasConsumed
                        let isUnsupported := actualExit = Excno.invOpcode.toInt
                        let mismatches0 : Array String := #[]
                        let mismatches1 :=
                          if actualExit ≠ tc.expected.exit_code then
                            mismatches0.push s!"exit_code expected={tc.expected.exit_code} actual={actualExit}"
                          else
                            mismatches0
                        let mismatches :=
                          match tc.expected.gas_used with
                          | some expGas =>
                              if gasUsed ≠ expGas then
                                mismatches1.push s!"gas_used expected={expGas} actual={gasUsed}"
                              else
                                mismatches1
                          | none => mismatches1

                        let status : DiffStatus :=
                          if isUnsupported && cfg.skipUnsupported then
                            .skip
                          else if mismatches.isEmpty then
                            .pass
                          else
                            .fail
                        let err : Option String :=
                          if status == .fail then
                            some (String.intercalate "; " mismatches.toList)
                          else
                            none
                        { tx_hash := tc.tx_hash
                          status
                          expected_exit_code := tc.expected.exit_code
                          actual_exit_code := some actualExit
                          expected_gas_used := tc.expected.gas_used
                          actual_gas_used := some gasUsed
                          error := err }

                      let attachExpectedCells (base : TestResult) (stF : VmState) : IO TestResult := do
                        if base.status == .skip then
                          return base
                        let mut mismatches : Array String := #[]

                        match tc.expected.c4_boc with
                        | some s =>
                            match decodeBytes s with
                            | .error e => mismatches := mismatches.push s!"expected.c4_boc decode: {e}"
                            | .ok bytes =>
                                match stdBocDeserialize bytes with
                                | .error e => mismatches := mismatches.push s!"expected.c4_boc parse: {e}"
                                | .ok exp =>
                                    if !(stF.regs.c4 == exp) then
                                      mismatches := mismatches.push "c4 mismatch"
                        | none => pure ()

                        match tc.expected.c5_boc with
                        | some s =>
                            match decodeBytes s with
                            | .error e => mismatches := mismatches.push s!"expected.c5_boc decode: {e}"
                            | .ok bytes =>
                                match stdBocDeserialize bytes with
                                | .error e => mismatches := mismatches.push s!"expected.c5_boc parse: {e}"
                                | .ok exp =>
                                    if !(stF.regs.c5 == exp) then
                                      mismatches := mismatches.push "c5 mismatch"
                        | none => pure ()

                        match tc.expected.c7 with
                        | some expC7 =>
                            match expC7.toValue with
                            | .error e => mismatches := mismatches.push s!"expected.c7: {e}"
                            | .ok v =>
                                match v with
                                | .tuple items =>
                                    if !(arrayBeq stF.regs.c7 items) then
                                      mismatches := mismatches.push "c7 mismatch"
                                | _ =>
                                    mismatches := mismatches.push "expected.c7: expected tuple"
                        | none => pure ()

                        if mismatches.isEmpty then
                          return base
                        else
                          let msg := String.intercalate "; " mismatches.toList
                          let err :=
                            match base.error with
                            | some prev => some (prev ++ "; " ++ msg)
                            | none => some msg
                          return { base with status := .fail, error := err }

                      if cfg.traceAll then
                        let (res, t, wrapped) := VmState.runTrace cfg.fuel st0 cfg.traceMax
                        match res with
                        | .continue _ =>
                            return {
                              tx_hash := tc.tx_hash
                              status := .fail
                              expected_exit_code := tc.expected.exit_code
                              expected_gas_used := tc.expected.gas_used
                              error := some "fuel exhausted"
                              trace := some t
                              trace_truncated := some wrapped
                            }
                        | .halt exitCode stF =>
                            let base := mkBase exitCode stF
                            let base ← attachExpectedCells base stF
                            return { base with trace := some t, trace_truncated := some wrapped }
                      else
                        match VmState.run cfg.fuel st0 with
                        | .continue _ =>
                            return {
                              tx_hash := tc.tx_hash
                              status := .fail
                              expected_exit_code := tc.expected.exit_code
                              expected_gas_used := tc.expected.gas_used
                              error := some "fuel exhausted"
                            }
                        | .halt exitCode stF =>
                            let base := mkBase exitCode stF
                            let base ← attachExpectedCells base stF

                            if cfg.traceFailures && base.status ≠ .pass then
                              let (_, t, wrapped) := VmState.runTrace cfg.fuel st0 cfg.traceMax
                              return { base with trace := some t, trace_truncated := some wrapped }
                            else
                              return base

end TvmLean
