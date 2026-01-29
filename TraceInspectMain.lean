import TvmLean.DiffTest

open TvmLean
open Lean

structure CliOpts where
  casePath? : Option System.FilePath := none
  fuel : Nat := 1_000_000
  gasLimit : Int := 1_000_000
  stopStep? : Option Nat := none
  eventContains? : Option String := none
  showTop : Nat := 6
  stopAfterMatch : Bool := true
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
  | "--stop-step" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with stopStep? := some v }
      | none => throw (IO.userError s!"invalid --stop-step {n}")
  | "--event-contains" :: s :: rest =>
      parseArgs rest { opts with eventContains? := some s }
  | "--show-top" :: n :: rest =>
      match n.toNat? with
      | some v => parseArgs rest { opts with showTop := v }
      | none => throw (IO.userError s!"invalid --show-top {n}")
  | "--stop-after-match" :: rest =>
      parseArgs rest { opts with stopAfterMatch := true }
  | "--no-stop-after-match" :: rest =>
      parseArgs rest { opts with stopAfterMatch := false }
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

def sliceAddrStdSummary? (s : Slice) : Option String :=
  match
    (do
      let (tag, s2) ← s.takeBitsAsNatCellUnd 2
      if tag != 2 then
        throw .cellUnd
      let s3 ← s2.skipMaybeAnycast
      let (wcNat, sWc) ← s3.takeBitsAsNatCellUnd 8
      if !sWc.haveBits 256 then
        throw .cellUnd
      let addrBits := sWc.readBits 256
      let wc : Int := natToIntSignedTwos wcNat 8
      let addrHex : String :=
        bytesToHex (bitStringToBytesBE addrBits)
      return s!"addr_std wc={wc} addr=0x{addrHex}"
      : Except Excno String)
  with
  | .ok s => some s
  | .error _ => none

def valueDebug (v : Value) : String :=
  match v with
  | .null => "null"
  | .int .nan => "NaN"
  | .int (.num n) => s!"int({n})"
  | .cell c =>
      let refsSummary :=
        if c.refs.isEmpty then
          ""
        else
          Id.run do
            let mut parts : Array String := #[]
            for i in [0:c.refs.size] do
              let r := c.refs[i]!
              parts := parts.push s!"{i}:special={r.special} hash={cellHashHex r}"
            return s!" refs=[{String.intercalate "," parts.toList}]"
      s!"cell(bits={c.bits.size},refs={c.refs.size},special={c.special},lm={c.levelMask},hash={cellHashHex c}){refsSummary}"
  | .builder b =>
      let refsSummary :=
        if b.refs.isEmpty then
          ""
        else
          Id.run do
            let mut parts : Array String := #[]
            for i in [0:b.refs.size] do
              let c := b.refs[i]!
              parts := parts.push s!"{i}:special={c.special} hash={cellHashHex c}"
            return s!" refs=[{String.intercalate "," parts.toList}]"
      s!"builder(bits={b.bits.size},refs={b.refs.size}){refsSummary}"
  | .tuple t => s!"tuple({t.size})"
  | .cont _ => "cont(..)"
  | .slice s =>
      let base :=
        s!"slice(bitPos={s.bitPos},refPos={s.refPos},bitsRem={s.bitsRemaining},refsRem={s.refsRemaining},cellHash={cellHashHex s.cell})"
      match sliceAddrStdSummary? (Slice.ofCell (s.toCellRemaining)) with
      | some a => base ++ s!" {a}"
      | none => base

def dumpTop (title : String) (stack : Stack) (n : Nat) : IO Unit := do
  IO.println s!"{title} stack_size={stack.size}"
  let k := min n stack.size
  let start := stack.size - k
  for i in [0:k] do
    let idx := start + i
    let fromTop := stack.size - 1 - idx
    let v := stack[idx]!
    IO.println s!"  s{fromTop} = {valueDebug v}"

def buildVmState (opts : CliOpts) (tc : TestCase) : IO VmState := do
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
  pure st0

partial def containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then
    true
  else
    let h := haystack.data
    let n := needle.data
    let nLen := n.length
    let hLen := h.length
    let rec go (i : Nat) : Bool :=
      if i + nLen > hLen then
        false
      else if (h.drop i).take nLen == n then
        true
      else
        go (i + 1)
    go 0

def shouldDump (opts : CliOpts) (step : Nat) (event : String) : Bool :=
  let stepOk :=
    match opts.stopStep? with
    | none => false
    | some s => s = step
  let eventOk :=
    match opts.eventContains? with
    | none => false
    | some sub => containsSubstr event sub
  stepOk || eventOk

def main (args : List String) : IO Unit := do
  let opts ← parseArgs args
  let casePath ←
    match opts.casePath? with
    | some p => pure p
    | none => throw (IO.userError "missing required argument: --case <file.json>")

  let tc ← loadTestCase casePath
  IO.println s!"tx_hash={tc.tx_hash}"
  let mut st ← buildVmState opts tc

  let mut step : Nat := 0
  let mut fuel := opts.fuel
  while fuel > 0 do
    let stBefore := st
    let (entry, res) := stBefore.stepTrace step
    let stAfter :=
      match res with
      | .continue s => s
      | .halt _ s => s

    if shouldDump opts step entry.event then
      IO.println s!"step={step} event={entry.event} cp={entry.cp}"
      IO.println s!"  cc_before={entry.cc_before}"
      IO.println s!"  cc_after ={entry.cc_after}"
      IO.println s!"  gas_before={entry.gas_before} gas_after={entry.gas_after}"
      dumpTop "before" stBefore.stack opts.showTop
      dumpTop "after" stAfter.stack opts.showTop
      if opts.stopAfterMatch then
        fuel := 0
      else
        pure ()

    match res with
    | .continue s =>
        st := s
        step := step + 1
        fuel := fuel - 1
    | .halt exitCode s =>
        let actualExit : Int := ~~~ exitCode
        IO.println s!"halt exit_code={actualExit} committed={s.cstate.committed} gas_used={s.gas.gasConsumed}"
        fuel := 0
