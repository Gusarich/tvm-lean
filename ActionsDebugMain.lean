import TvmLean.DiffTest
import TvmLean.CellDiff

open TvmLean
open Lean

structure CliOpts where
  casePath? : Option System.FilePath := none
  fuel : Nat := 1_000_000
  gasLimit : Int := 1_000_000
  traceMax : Nat := 0
  maxActions : Nat := 20
  deriving Repr

partial def parseArgs (args : List String) (opts : CliOpts := {}) : IO CliOpts :=
  match args with
  | [] => pure opts
  | "--case" :: path :: rest =>
      parseArgs rest { opts with casePath? := some path }
  | "--fuel" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with fuel := v }
      | none => throw (IO.userError s!"invalid --fuel {n}")
  | "--gas-limit" :: n :: rest =>
      match n.toInt? with
      | some v => parseArgs rest { opts with gasLimit := v }
      | none => throw (IO.userError s!"invalid --gas-limit {n}")
  | "--max-actions" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with maxActions := v }
      | none => throw (IO.userError s!"invalid --max-actions {n}")
  | "--" :: rest =>
      parseArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")

def byteToHex (b : UInt8) : String :=
  let hex : Array Char := "0123456789abcdef".data.toArray
  let hi : Nat := (b.toNat / 16) % 16
  let lo : Nat := b.toNat % 16
  String.mk [hex[hi]!, hex[lo]!]

def bytesToHex (bs : Array UInt8) : String :=
  String.join (bs.toList.map byteToHex)

def cellHashHex (c : Cell) : String :=
  bytesToHex (Cell.hashBytes c)

def cellSummary (c : Cell) : String :=
  s!"bits={c.bits.size} refs={c.refs.size} hash={cellHashHex c}"

inductive ParsedAction where
  | sendRawMsg (mode : Nat) (msg : Cell)
  | reserve (mode : Nat) (grams : Nat) (extra : Option Cell)
  | unknown (tag : Nat) (cell : Cell)
  deriving Repr

def parseVarUInteger16 (s : Slice) : Except Excno (Nat × Slice) := do
  let (lenBytes, s1) ← s.takeBitsAsNatCellUnd 4
  let (v, s2) ← s1.takeBitsAsNatCellUnd (lenBytes * 8)
  return (v, s2)

def parseActionNode (c : Cell) : Except Excno ParsedAction := do
  let s0 := Slice.ofCell c
  let (tag, s1) ← s0.takeBitsAsNatCellUnd 32
  if tag = 0x0ec3c86d then
    let (mode, _) ← s1.takeBitsAsNatCellUnd 8
    if h : 1 < c.refs.size then
      return .sendRawMsg mode (c.refs[1]!)
    else
      throw .cellUnd
  else if tag = 0x36e6b809 then
    let (mode, s2) ← s1.takeBitsAsNatCellUnd 8
    let (grams, s3) ← parseVarUInteger16 s2
    let (hasExtra, _) ← s3.takeBitsAsNatCellUnd 1
    let extra :=
      if hasExtra = 0 then
        none
      else
        if h : 1 < c.refs.size then
          some (c.refs[1]!)
        else
          none
    return .reserve mode grams extra
  else
    return .unknown tag c

partial def parseOutList (c5 : Cell) : Except Excno (Array ParsedAction) := do
  let mut cur : Cell := c5
  let mut out : Array ParsedAction := #[]
  while !(cur.bits.isEmpty && cur.refs.isEmpty) do
    if cur.refs.isEmpty then
      throw .cellUnd
    let a ← parseActionNode cur
    out := out.push a
    cur := cur.refs[0]!
  return out

def actionSummary : ParsedAction → String
  | .sendRawMsg mode msg =>
      s!"SENDRAWMSG mode={mode} msg({cellSummary msg})"
  | .reserve mode grams extra =>
      let extraStr :=
        match extra with
        | some c => s!" extra({cellSummary c})"
        | none => " extra=none"
      s!"RAWRESERVE mode={mode} grams={grams}{extraStr}"
  | .unknown tag cell =>
      s!"UNKNOWN tag=0x{Nat.toDigits 16 tag |> String.mk} ({cellSummary cell})"

def summarizeActions (title : String) (acts : Array ParsedAction) (max : Nat) : IO Unit := do
  IO.println s!"{title}: count={acts.size}"
  let n := min max acts.size
  let mut i : Nat := 0
  while i < n do
    match acts[i]? with
    | some a => IO.println s!"  [{i}] {actionSummary a}"
    | none => IO.println s!"  [{i}] <missing>"
    i := i + 1
  if acts.size > n then
    IO.println s!"  ... ({acts.size - n} more)"

def loadAndRun (opts : CliOpts) (tc : TestCase) : IO (Cell × Bool × VmState) := do
  let codeBytes ←
    match decodeBytes tc.code_boc with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"code_boc decode: {e}")
  let dataBytes ←
    match decodeBytes tc.data_boc with
    | .ok b => pure b
    | .error e => throw (IO.userError s!"data_boc decode: {e}")
  let codeCell ←
    match stdBocDeserialize codeBytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"code_boc parse: {e}")
  let dataCell ←
    match stdBocDeserialize dataBytes with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"data_boc parse: {e}")
  let initStack ←
    match buildInitStack tc.stack_init with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"stack_init: {e}")
  let initC7 : Array Value :=
    match tc.expected.c7 with
    | none => defaultInitC7 tc.stack_init codeCell
    | some expC7 =>
        match expC7.toValue with
        | .ok (.tuple items) => items
        | .ok _ => defaultInitC7 tc.stack_init codeCell
        | .error _ => defaultInitC7 tc.stack_init codeCell

  let gasLimitInit : Int := tc.expected.gas_limit.getD opts.gasLimit
  let gasMax0 : Int := tc.expected.gas_max.getD opts.gasLimit
  let gasMaxInit : Int := if gasMax0 < gasLimitInit then gasLimitInit else gasMax0
  let gasCreditInit : Int := tc.expected.gas_credit.getD 0
  let base := VmState.initial codeCell gasLimitInit gasMaxInit gasCreditInit
  let st0 : VmState :=
    { base with stack := initStack, regs := { base.regs with c4 := dataCell, c7 := initC7 } }

  match VmState.run opts.fuel st0 with
  | .continue _ =>
      throw (IO.userError "fuel exhausted")
  | .halt exitCode stF =>
      let actualExit : Int := ~~~ exitCode
      if actualExit ≠ tc.expected.exit_code then
        IO.println s!"warning: exit_code expected={tc.expected.exit_code} actual={actualExit}"
      let okData : Bool := (stF.gas.gasCredit == 0) && stF.cstate.committed
      let finalC5 : Cell := if okData then stF.cstate.c5 else Cell.empty
      return (finalC5, okData, stF)

def main (args : List String) : IO Unit := do
  let opts ← parseArgs args
  let casePath ←
    match opts.casePath? with
    | some p => pure p
    | none => throw (IO.userError "missing required argument: --case <file.json>")
  let tc ← loadTestCase casePath

  IO.println s!"tx_hash={tc.tx_hash}"

  let (finalC5, okData, stF) ← loadAndRun opts tc
  IO.println s!"okData={okData} committed={stF.cstate.committed} gas_credit={stF.gas.gasCredit} c5_final({cellSummary finalC5})"

  let expC5 ←
    match tc.expected.c5_boc with
    | none => throw (IO.userError "fixture missing expected.c5_boc")
    | some s =>
        match decodeBytes s with
        | .error e => throw (IO.userError s!"expected.c5_boc decode: {e}")
        | .ok bytes =>
            match stdBocDeserialize bytes with
            | .error e => throw (IO.userError s!"expected.c5_boc parse: {e}")
            | .ok c => pure c

  IO.println s!"c5_expected({cellSummary expC5})"

  let expActs ←
    match parseOutList expC5 with
    | .ok a => pure a
    | .error e => do
        IO.println s!"warning: failed to parse expected action list: {e}"
        pure #[]
  let actActs ←
    match parseOutList finalC5 with
    | .ok a => pure a
    | .error e => do
        IO.println s!"warning: failed to parse actual action list: {e}"
        pure #[]

  summarizeActions "expected actions (head->tail)" expActs opts.maxActions
  summarizeActions "actual actions (head->tail)" actActs opts.maxActions

  if expC5 == finalC5 then
    IO.println "c5: EXACT MATCH"
  else
    IO.println "c5: MISMATCH"
    match Cell.diff expC5 finalC5 with
    | some msg => IO.println s!"first diff: {msg}"
    | none => IO.println "first diff: <none> (unexpected)"
