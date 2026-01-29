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

def addrCellSummary (c : Cell) : Option String :=
  let s0 := Slice.ofCell c
  match
    (show Except Excno String from do
      let (tag, s2) ← s0.takeBitsAsNatCellUnd 2
      match tag with
      | 0 => return "addr_none"
      | 2 =>
          let s3 ← s2.skipMaybeAnycast
          let (wcNat, sWc) ← s3.takeBitsAsNatCellUnd 8
          if !sWc.haveBits 256 then
            throw .cellUnd
          let wc : Int := natToIntSignedTwos wcNat 8
          let addrHex := bytesToHex (bitStringToBytesBE (sWc.readBits 256))
          return s!"addr_std wc={wc} addr=0x{addrHex}"
      | 3 =>
          let s3 ← s2.skipMaybeAnycast
          let (addrLen, sLen) ← s3.takeBitsAsNatCellUnd 9
          let (wcNat, sWc) ← sLen.takeBitsAsNatCellUnd 32
          if !sWc.haveBits addrLen then
            throw .cellUnd
          let wc : Int := natToIntSignedTwos wcNat 32
          return s!"addr_var wc={wc} addr_len={addrLen}"
      | _ => throw .cellUnd) with
  | .ok s => some s
  | .error _ => none

inductive ParsedAction where
  | sendRawMsg (mode : Nat) (msg : Cell)
  | reserve (mode : Nat) (grams : Nat) (extra : Option Cell)
  | unknown (tag : Nat) (cell : Cell)
  deriving Repr

def parseVarUInteger16 (s : Slice) : Except Excno (Nat × Slice) := do
  let (lenBytes, s1) ← s.takeBitsAsNatCellUnd 4
  let (v, s2) ← s1.takeBitsAsNatCellUnd (lenBytes * 8)
  return (v, s2)

def parseBodyOpQid? (body : Cell) : Option (Nat × Nat) :=
  match (show Except Excno (Nat × Nat) from do
      let s0 := Slice.ofCell body
      let (op, s1) ← s0.takeBitsAsNatCellUnd 32
      let (qid, _) ← s1.takeBitsAsNatCellUnd 64
      return (op, qid)) with
  | .ok v => some v
  | .error _ => none

def cellBitsPrefixHex (c : Cell) (maxBytes : Nat) : String :=
  let bytesAvail : Nat := c.bits.size / 8
  let n : Nat := min maxBytes bytesAvail
  bytesToHex (bitStringToBytesBE (c.bits.take (n * 8)))

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

def parseMessageSummary (msg : Cell) : Except Excno String := do
  let s0 := Slice.ofCell msg
  let (b0, s1) ← s0.takeBitsAsNatCellUnd 1
  if b0 = 0 then
    -- int_msg_info$0 ihr_disabled bounce bounced ...
    let (ihrDisabled, s2) ← s1.takeBitsAsNatCellUnd 1
    let (bounce, s3) ← s2.takeBitsAsNatCellUnd 1
    let (bounced, s4) ← s3.takeBitsAsNatCellUnd 1

    let srcStart := s4
    let srcStop ← srcStart.skipMessageAddr
    let srcCell := Slice.prefixCell srcStart srcStop

    let destStart := srcStop
    let destStop ← destStart.skipMessageAddr
    let destCell := Slice.prefixCell destStart destStop
    let srcAddrStr := (addrCellSummary srcCell).getD s!"0x{cellHashHex srcCell}"
    let destAddrStr := (addrCellSummary destCell).getD s!"0x{cellHashHex destCell}"

    let (valueGrams, afterValue) ← destStop.takeCurrencyCollectionGramsCellUnd
    let (_, afterFlags) ← afterValue.takeVarUIntegerCellUnd 4 -- extra_flags:(VarUInteger 16)
    let (fwdFee, afterFee) ← afterFlags.takeGramsCellUnd
    let (createdLt, afterLt) ← afterFee.takeBitsAsNatCellUnd 64
    let (createdAt, afterAt) ← afterLt.takeBitsAsNatCellUnd 32

    -- init:(Maybe (Either StateInit ^StateInit))
    let (hasInit, afterHasInit) ← afterAt.takeBitsAsNatCellUnd 1
    let (initStr, afterInit) ←
      if hasInit = 0 then
        pure ("none", afterHasInit)
      else
        let (isRef, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
        if isRef = 1 then
          if !afterEither.haveRefs 1 then
            throw .cellUnd
          let c := afterEither.cell.refs[afterEither.refPos]!
          pure (s!"ref({cellHashHex c})", { afterEither with refPos := afterEither.refPos + 1 })
        else
          let stStart := afterEither
          let stStop ← stStart.skipStateInitCellUnd
          let stCell := Slice.prefixCell stStart stStop
          pure (s!"inline({cellHashHex stCell})", stStop)

    -- body:(Either X ^X)
    let bodyStr : String ←
      if !afterInit.haveBits 1 then
        pure "<missing>"
      else
        let (bodyTag, afterBodyTag) ← afterInit.takeBitsAsNatCellUnd 1
        if bodyTag = 0 then
          pure s!"inline(bits={afterBodyTag.bitsRemaining},refs={afterBodyTag.refsRemaining})"
        else
          if afterBodyTag.haveRefs 1 then
            let c := afterBodyTag.cell.refs[afterBodyTag.refPos]!
            pure s!"ref({cellHashHex c})"
          else
            pure "<missing_ref>"

    return (s!"int ihr_disabled={ihrDisabled} bounce={bounce} bounced={bounced} src={srcAddrStr} dest={destAddrStr} " ++
      s!"value_grams={valueGrams} fwd_fee={fwdFee} created_lt={createdLt} created_at={createdAt} init={initStr} body={bodyStr}")
  else
    let (b1, _) ← s1.takeBitsAsNatCellUnd 1
    if b1 = 0 then
      return "ext_in_msg_info$10 ..."
    else
      return "ext_out_msg_info$11 ..."

def extractInitBodyRefs? (msg : Cell) : Except Excno (Option Cell × Option Cell) := do
  let s0 := Slice.ofCell msg
  let (b0, s1) ← s0.takeBitsAsNatCellUnd 1
  let afterInfo ←
    if b0 = 0 then
      -- Internal message.
      let (_, s2) ← s1.takeBitsAsNatCellUnd 3 -- ihr_disabled + bounce + bounced
      let afterSrc ← s2.skipMessageAddr
      let afterDest ← afterSrc.skipMessageAddr
      let (_, afterValue) ← afterDest.takeCurrencyCollectionGramsCellUnd
      let (_, afterFlags) ← afterValue.takeVarUIntegerCellUnd 4
      let (_, afterFee) ← afterFlags.takeGramsCellUnd
      let (_, afterLt) ← afterFee.takeBitsAsNatCellUnd 64
      let (_, afterAt) ← afterLt.takeBitsAsNatCellUnd 32
      pure afterAt
    else
      let (b1, s2) ← s1.takeBitsAsNatCellUnd 1
      if b1 = 1 then
        -- External outbound message.
        let afterSrc ← s2.skipMessageAddr
        let afterDest ← afterSrc.skipMessageAddr
        let (_, afterLt) ← afterDest.takeBitsAsNatCellUnd 64
        let (_, afterAt) ← afterLt.takeBitsAsNatCellUnd 32
        pure afterAt
      else
        throw .cellUnd

  -- init:(Maybe (Either StateInit ^StateInit))
  let (hasInit, afterHasInit) ← afterInfo.takeBitsAsNatCellUnd 1
  let (initRef?, afterInit) ←
    if hasInit = 0 then
      pure (none, afterHasInit)
    else
      let (isRef, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
      if isRef = 1 then
        if afterEither.haveRefs 1 then
          let c := afterEither.cell.refs[afterEither.refPos]!
          pure (some c, { afterEither with refPos := afterEither.refPos + 1 })
        else
          throw .cellUnd
      else
        -- inline StateInit; just skip it
        let stStop ← afterEither.skipStateInitCellUnd
        pure (none, stStop)

  -- body:(Either X ^X)
  if !afterInit.haveBits 1 then
    return (initRef?, none)
  let (bodyTag, afterBodyTag) ← afterInit.takeBitsAsNatCellUnd 1
  if bodyTag = 1 then
    if afterBodyTag.haveRefs 1 then
      let c := afterBodyTag.cell.refs[afterBodyTag.refPos]!
      return (initRef?, some c)
    else
      throw .cellUnd
  else
    return (initRef?, none)

def compareActions (expActs actActs : Array ParsedAction) : IO Unit := do
  let n := min expActs.size actActs.size
  let mut i : Nat := 0
  while i < n do
    match expActs[i]?, actActs[i]? with
    | some (.sendRawMsg modeE msgE), some (.sendRawMsg modeA msgA) =>
        if modeE != modeA then
          IO.println s!"action[{i}]: SENDRAWMSG mode mismatch expected={modeE} actual={modeA}"
        if msgE != msgA then
          IO.println s!"action[{i}]: SENDRAWMSG msg mismatch expected={cellHashHex msgE} actual={cellHashHex msgA}"
          match parseMessageSummary msgE, parseMessageSummary msgA with
          | .ok se, .ok sa =>
              IO.println s!"  expected: {se}"
              IO.println s!"  actual:   {sa}"
          | .error ee, _ =>
              IO.println s!"  expected: <parse error {ee}>"
          | _, .error ea =>
              IO.println s!"  actual:   <parse error {ea}>"
          match Cell.diff msgE msgA with
          | some d => IO.println s!"  first msg diff: {d}"
          | none => IO.println "  first msg diff: <none>"
          match extractInitBodyRefs? msgE, extractInitBodyRefs? msgA with
          | .ok (initE?, bodyE?), .ok (initA?, bodyA?) =>
              match initE?, initA? with
              | some ce, some ca =>
                  if ce != ca then
                    IO.println s!"  init ref diff: {(Cell.diff ce ca).getD "<none>"}"
                    let dumpInit (label : String) (c : Cell) : IO Unit := do
                      IO.println s!"    {label} init({cellSummary c})"
                      for j in [0:c.refs.size] do
                        let r := c.refs[j]!
                        let tyByte :=
                          if r.bits.size ≥ 8 then
                            bitsToNat (r.bits.take 8)
                          else
                            0
                        let extra :=
                          if r.special && tyByte = 2 && r.bits.size = 8 + 256 then
                            let libHashBits := r.bits.extract 8 (8 + 256)
                            let libHashHex := bytesToHex (bitStringToBytesBE libHashBits)
                            s!" libHash=0x{libHashHex}"
                          else
                            ""
                        IO.println s!"      {label} init.refs[{j}] bits={r.bits.size} refs={r.refs.size} special={r.special} tyByte={tyByte} hash={cellHashHex r}{extra}"
                    dumpInit "expected" ce
                    dumpInit "actual" ca
              | _, _ => pure ()
              match bodyE?, bodyA? with
              | some ce, some ca =>
                  if ce != ca then
                    IO.println s!"  body ref diff: {(Cell.diff ce ca).getD "<none>"}"
                    match parseBodyOpQid? ce, parseBodyOpQid? ca with
                    | some (opE, qidE), some (opA, qidA) =>
                        IO.println s!"    body op/qid expected=0x{natToHexPad opE 8}/0x{natToHexPad qidE 16} actual=0x{natToHexPad opA 8}/0x{natToHexPad qidA 16}"
                    | _, _ => pure ()
                    if !ce.refs.isEmpty && !ca.refs.isEmpty then
                      let rE := ce.refs[0]!
                      let rA := ca.refs[0]!
                      IO.println s!"    body.refs[0] expected({cellSummary rE}) actual({cellSummary rA})"
                      IO.println s!"      body.refs[0] bits_prefix expected=0x{cellBitsPrefixHex rE 24} actual=0x{cellBitsPrefixHex rA 24}"
                      match parseBodyOpQid? rE, parseBodyOpQid? rA with
                      | some (opE, qidE), some (opA, qidA) =>
                          IO.println s!"      body.refs[0] op/qid expected=0x{natToHexPad opE 8}/0x{natToHexPad qidE 16} actual=0x{natToHexPad opA 8}/0x{natToHexPad qidA 16}"
                      | _, _ => pure ()
              | _, _ => pure ()
          | _, _ => pure ()
    | some (.reserve modeE gramsE extraE), some (.reserve modeA gramsA extraA) =>
        if modeE != modeA || gramsE != gramsA || extraE != extraA then
          IO.println s!"action[{i}]: RAWRESERVE mismatch expected={actionSummary (.reserve modeE gramsE extraE)} actual={actionSummary (.reserve modeA gramsA extraA)}"
    | some e, some a =>
        if reprStr e != reprStr a then
          IO.println s!"action[{i}]: type mismatch expected={actionSummary e} actual={actionSummary a}"
    | _, _ => pure ()
    i := i + 1

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

def loadAndRun (opts : CliOpts) (tc : TestCase) : IO (Cell × Cell × Bool × VmState) := do
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
      let finalC4 : Cell := if okData then stF.cstate.c4 else dataCell
      let finalC5 : Cell := if okData then stF.cstate.c5 else Cell.empty
      return (finalC4, finalC5, okData, stF)

def main (args : List String) : IO Unit := do
  let opts ← parseArgs args
  let casePath ←
    match opts.casePath? with
    | some p => pure p
    | none => throw (IO.userError "missing required argument: --case <file.json>")
  let tc ← loadTestCase casePath

  IO.println s!"tx_hash={tc.tx_hash}"

  -- Helpful when debugging wallet-like contracts: many outcomes are derived from the inbound body.
  match decodeBytes tc.stack_init.in_msg_body_boc with
  | .error e => IO.println s!"in_msg_body_boc decode error: {e}"
  | .ok b =>
      match stdBocDeserialize b with
      | .error e => IO.println s!"in_msg_body_boc parse error: {e}"
      | .ok body =>
          IO.println s!"in_msg_body({cellSummary body})"
          match parseBodyOpQid? body with
          | some (op, qid) =>
              IO.println s!"  in_msg_body op/qid=0x{natToHexPad op 8}/0x{natToHexPad qid 16}"
          | none => pure ()
          if !body.refs.isEmpty then
            let r0 := body.refs[0]!
            IO.println s!"  in_msg_body.refs[0]({cellSummary r0}) prefix=0x{cellBitsPrefixHex r0 24}"
            match parseBodyOpQid? r0 with
            | some (op, qid) =>
                IO.println s!"    in_msg_body.refs[0] op/qid=0x{natToHexPad op 8}/0x{natToHexPad qid 16}"
            | none => pure ()

  let (finalC4, finalC5, okData, stF) ← loadAndRun opts tc
  IO.println s!"okData={okData} committed={stF.cstate.committed} gas_credit={stF.gas.gasCredit} c4_final({cellSummary finalC4}) c5_final({cellSummary finalC5})"

  match tc.expected.c4_boc with
  | none => IO.println "c4_expected: <missing>"
  | some s =>
      match decodeBytes s with
      | .error e => IO.println s!"c4_expected decode error: {e}"
      | .ok bytes =>
          match stdBocDeserialize bytes with
          | .error e => IO.println s!"c4_expected parse error: {e}"
          | .ok expC4 =>
              IO.println s!"c4_expected({cellSummary expC4})"
              if expC4 == finalC4 then
                IO.println "c4: EXACT MATCH"
              else
                IO.println "c4: MISMATCH"
                IO.println s!"  bits_prefix expected=0x{cellBitsPrefixHex expC4 48} actual=0x{cellBitsPrefixHex finalC4 48}"
                match Cell.diff expC4 finalC4 with
                | some msg => IO.println s!"  first diff: {msg}"
                | none => IO.println "  first diff: <none> (unexpected)"

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
  compareActions expActs actActs

  if expC5 == finalC5 then
    IO.println "c5: EXACT MATCH"
  else
    IO.println "c5: MISMATCH"
    match Cell.diff expC5 finalC5 with
    | some msg => IO.println s!"first diff: {msg}"
    | none => IO.println "first diff: <none> (unexpected)"
