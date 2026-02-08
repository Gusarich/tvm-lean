import Lean
import TvmLean.Model
import TvmLean.Semantics
import TvmLean.Boc
import TvmLean.Native
import TvmLean.Validation.Canon.Value
import TvmLean.Validation.Diff.Schema
import TvmLean.Validation.Diff.Report

namespace TvmLean

open Lean

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

def tupleSetExtend (t : Array Value) (idx : Nat) (v : Value) : Array Value :=
  if idx < t.size then
    t.set! idx v
  else
    (t ++ Array.replicate (idx - t.size) Value.null).push v

def extractMyAddrFromInMsg? (msgCell : Cell) : Option Slice :=
  let s0 : Slice := Slice.ofCell msgCell
  let parsed : Except Excno Slice := do
    let (b0, s1) ← s0.takeBitsAsNatCellUnd 1
    if b0 = 0 then
      -- int_msg_info$0 ihr_disabled bounce bounced src dest ...
      if !s1.haveBits 3 then
        throw .cellUnd
      let afterFlags := s1.advanceBits 3
      let afterSrc ← afterFlags.skipMessageAddr
      let destStart := afterSrc
      let destStop ← destStart.skipMessageAddr
      let addrCell := Slice.prefixCell destStart destStop
      return Slice.ofCell addrCell
    else
      let (b1, s2) ← s1.takeBitsAsNatCellUnd 1
      if b1 = 0 then
        -- ext_in_msg_info$10 src:(MsgAddressExt) dest:(MsgAddressInt) ...
        let afterSrc ← s2.skipMessageAddr
        let destStart := afterSrc
        let destStop ← destStart.skipMessageAddr
        let addrCell := Slice.prefixCell destStart destStop
        return Slice.ofCell addrCell
      else
        -- ext_out_msg_info$11 src:(MsgAddressInt) dest:(MsgAddressExt) ...
        -- For such messages, the contract address is the `src`.
        let srcStart := s2
        let srcStop ← srcStart.skipMessageAddr
        let addrCell := Slice.prefixCell srcStart srcStop
        return Slice.ofCell addrCell
  match parsed with
  | .ok s => some s
  | .error _ => none

def defaultInMsgParams (si : StackInit) : Array Value :=
  -- Conservative default that stays in-range for `tuple_index`-style accesses.
  -- We at least propagate `msg_balance_grams` as the "remaining value" field.
  let addrNone : Value :=
    let cell : Cell := Cell.mkOrdinary #[false, false] #[]
    .slice (Slice.ofCell cell)
  #[
    .int (.num 0),                  -- bounce
    .int (.num 0),                  -- bounced
    addrNone,                       -- src_addr
    .int (.num 0),                  -- fwd_fee
    .int (.num 0),                  -- created_lt
    .int (.num 0),                  -- created_at
    .int (.num 0),                  -- original value
    .int (.num si.msg_balance_grams), -- value
    .null,                          -- value extra
    .null                           -- state_init
  ]

def extractInMsgParamsFromInMsg? (si : StackInit) (msgCell : Cell) : Option (Array Value) :=
  let addrNone : Value :=
    let cell : Cell := Cell.mkOrdinary #[false, false] #[]
    .slice (Slice.ofCell cell)

  let s0 : Slice := Slice.ofCell msgCell
  let parsed : Except Excno (Array Value) := do
    let (b0, s1) ← s0.takeBitsAsNatCellUnd 1
    if b0 = 0 then
      -- int_msg_info$0 ihr_disabled:Bool bounce:Bool bounced:Bool ...
      let (_, s2) ← s1.takeBitsAsNatCellUnd 1 -- ihr_disabled
      let (bounceNat, s3) ← s2.takeBitsAsNatCellUnd 1
      let (bouncedNat, s4) ← s3.takeBitsAsNatCellUnd 1
      let bounceVal : Value := .int (.num (if bounceNat = 1 then -1 else 0))
      let bouncedVal : Value := .int (.num (if bouncedNat = 1 then -1 else 0))

      -- src:MsgAddressInt
      let srcStart := s4
      let srcStop ← srcStart.skipMessageAddr
      let srcCell := Slice.prefixCell srcStart srcStop
      let srcVal : Value := .slice (Slice.ofCell srcCell)

      -- dest:MsgAddressInt (skip)
      let afterDest ← srcStop.skipMessageAddr

      -- value:CurrencyCollection
      let (origGrams, afterValue) ← afterDest.takeCurrencyCollectionGramsCellUnd

      -- extra_flags:(VarUInteger 16) (skip)
      let (_, afterFlags) ← afterValue.takeVarUIntegerCellUnd 4

      -- fwd_fee:Grams
      let (fwdFee, afterFee) ← afterFlags.takeGramsCellUnd

      -- created_lt:uint64 created_at:uint32
      let (createdLtNat, afterLt) ← afterFee.takeBitsAsNatCellUnd 64
      let (createdAtNat, afterAt) ← afterLt.takeBitsAsNatCellUnd 32

      -- init:(Maybe (Either StateInit ^StateInit))
      let (hasInit, afterHasInit) ← afterAt.takeBitsAsNatCellUnd 1
      let stateInit? : Option Cell ←
        if hasInit = 0 then
          pure none
        else
          let (isRef, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
          if isRef = 1 then
            if !afterEither.haveRefs 1 then
              throw .cellUnd
            let c := afterEither.cell.refs[afterEither.refPos]!
            pure (some c)
          else
            let stStart := afterEither
            let stStop ← stStart.skipStateInitCellUnd
            let stCell := Slice.prefixCell stStart stStop
            pure (some stCell)

      let stateInitVal : Value :=
        match stateInit? with
        | none => .null
        | some c => .cell c

      let valueVal : Value := .int (.num si.msg_balance_grams)

      return #[
        bounceVal,
        bouncedVal,
        srcVal,
        .int (.num fwdFee),
        .int (.num (Int.ofNat createdLtNat)),
        .int (.num (Int.ofNat createdAtNat)),
        .int (.num origGrams),
        valueVal,
        .null,
        stateInitVal
      ]
    else
      let (b1, s2) ← s1.takeBitsAsNatCellUnd 1
      if b1 = 0 then
        -- ext_in_msg_info$10 src:(MsgAddressExt) dest:(MsgAddressInt) import_fee:Grams ...
        -- Transaction.cpp fabricates `in_msg_info` from this, with:
        -- - bounce/bounced = false
        -- - created_lt/created_at = 0
        -- - value = 0 (external messages cannot carry value)
        -- - fwd_fee is absent (treated as zero in `prepare_in_msg_params_tuple`)
        let bounceVal : Value := .int (.num 0)
        let bouncedVal : Value := .int (.num 0)

        let srcStart := s2
        let srcStop ← srcStart.skipMessageAddr
        let srcCell := Slice.prefixCell srcStart srcStop
        let srcVal : Value := .slice (Slice.ofCell srcCell)

        let afterDest ← srcStop.skipMessageAddr

        let (_, afterImportFee) ← afterDest.takeGramsCellUnd

        -- init:(Maybe (Either StateInit ^StateInit))
        let (hasInit, afterHasInit) ← afterImportFee.takeBitsAsNatCellUnd 1
        let stateInit? : Option Cell ←
          if hasInit = 0 then
            pure none
          else
            let (isRef, afterEither) ← afterHasInit.takeBitsAsNatCellUnd 1
            if isRef = 1 then
              if !afterEither.haveRefs 1 then
                throw .cellUnd
              let c := afterEither.cell.refs[afterEither.refPos]!
              pure (some c)
            else
              let stStart := afterEither
              let stStop ← stStart.skipStateInitCellUnd
              let stCell := Slice.prefixCell stStart stStop
              pure (some stCell)

        let stateInitVal : Value :=
          match stateInit? with
          | none => .null
          | some c => .cell c

        return #[
          bounceVal,
          bouncedVal,
          srcVal,
          .int (.num 0), -- fwd_fee
          .int (.num 0), -- created_lt
          .int (.num 0), -- created_at
          .int (.num 0), -- original value
          .int (.num si.msg_balance_grams), -- value (should be 0 for external inbound)
          .null,
          stateInitVal
        ]
      else
        -- ext_out_msg_info$11 ... (not an inbound message)
        return #[
          .int (.num 0),
          .int (.num 0),
          addrNone,
          .int (.num 0),
          .int (.num 0),
          .int (.num 0),
          .int (.num 0),
          .int (.num 0),
          .null,
          .null
        ]

  match parsed with
  | .ok t => some t
  | .error _ => none

def defaultInitC7 (si : StackInit) (codeCell : Cell) (myCodeCell : Cell := codeCell) : Array Value :=
  -- TON c7 initialization:
  -- - c7[0] is the environment tuple (`SmartContractInfo`, see TON docs `tvm/registers.md`)
  -- - c7[1..] are global variables (set via SETGLOB/SETGLOBVAR).
  --
  -- For strict diff tests, fixtures should include the relevant config params (18-21,24-25,43,45) so fee opcodes
  -- and precompiled gas accounting match on-chain behavior.
  let inMsgCell? : Option Cell :=
    match decodeBytes si.in_msg_boc with
    | .ok msgBytes =>
        match stdBocDeserialize msgBytes with
        | .ok msgCell => some msgCell
        | .error _ => none
    | .error _ => none

  let myAddrVal : Value :=
    match inMsgCell? with
    | some msgCell =>
        match extractMyAddrFromInMsg? msgCell with
        | some s => .slice s
        | none => .null
    | none => .null

  let configRootVal : Value :=
    match si.config_root_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .cell c
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let addrHashBytes : Array UInt8 :=
    match myAddrVal with
    | .slice addr =>
        match (do
          let s0 := addr
          let (tag, s2) ← s0.takeBitsAsNatCellUnd 2
          if tag != 2 then
            throw .cellUnd
          let s3 ← s2.skipMaybeAnycast
          let (_, s4) ← s3.takeBitsAsNatCellUnd 8 -- workchain_id:int8
          if !s4.haveBits 256 then
            throw .cellUnd
          let bits256 := s4.readBits 256
          let mut out : Array UInt8 := #[]
          for i in [0:32] do
            out := out.push (bitsToByte bits256 (i * 8) 8)
          return out : Except Excno (Array UInt8)) with
        | .ok bs => bs
        | .error _ => Array.replicate 32 0
    | _ => Array.replicate 32 0

  let randSeedVal : Value :=
    -- TON: RANDSEED = sha256(block_rand_seed . account_address) (256-bit).
    if decide (si.rand_seed < 0 ∨ si.rand_seed ≥ intPow2 256) then
      .int (.num 0)
    else
      let seedBytes := natToBytesBEFixed si.rand_seed.toNat 32
      let digest := sha256Digest (seedBytes ++ addrHashBytes)
      .int (.num (Int.ofNat (bytesToNatBE digest)))

  let inMsgParamsVal : Value :=
    match inMsgCell? with
    | some msgCell =>
        match extractInMsgParamsFromInMsg? si msgCell with
        | some t => .tuple t
        | none => .tuple (defaultInMsgParams si)
    | none => .tuple (defaultInMsgParams si)
  let params0 : Array Value :=
    #[.int (.num 0x076ef1ea), .int (.num 0), .int (.num 0)] -- magic, actions, msgs_sent
  let params1 := tupleSetExtend params0 3 (.int (.num si.now)) -- NOW
  -- TON: `block_lt` is the start logical time of the block containing this transaction (aligned by `lt_align = 1_000_000`).
  let blockLt : Int :=
    if decide (si.lt < 0) then
      0
    else
      si.lt - (si.lt % 1_000_000)
  let params2 := tupleSetExtend params1 4 (.int (.num blockLt)) -- BLOCKLT
  let params3 := tupleSetExtend params2 5 (.int (.num si.lt)) -- LTIME (tx lt)
  let params4 := tupleSetExtend params3 6 randSeedVal -- RANDSEED
  let params5 := tupleSetExtend params4 7 (.tuple #[.int (.num si.balance_grams), .null]) -- BALANCE
  let params6 := tupleSetExtend params5 8 myAddrVal -- MYADDR
  let params6 := tupleSetExtend params6 9 configRootVal -- CONFIGROOT
  -- `MYCODE` (c7 params[10]) is the code cell that is executed by the emulator.
  let params7 := tupleSetExtend params6 10 (.cell myCodeCell) -- MYCODE
  let params8 := tupleSetExtend params7 11 (.tuple #[.int (.num si.msg_balance_grams), .null]) -- INCOMINGVALUE
  let params9 := tupleSetExtend params8 12 (.int (.num si.storage_fees)) -- STORAGEFEES

  let bytesToBitsBE (bytes : Array UInt8) : BitString :=
    Id.run do
      let mut bits : BitString := #[]
      for b in bytes do
        bits := bits ++ natToBits b.toNat 8
      bits

  let precompiledGasUsageVal : Value :=
    -- ConfigParam 45 precompiled-contracts list → c7 params[16] (Maybe Integer).
    let codeHashBytes : Array UInt8 := Cell.hashBytes myCodeCell
    let codeHashBits : BitString := bytesToBitsBE codeHashBytes

    let lookupGasUsage? (cfgCell : Cell) : Option Nat :=
      match (do
        let cs0 := Slice.ofCell cfgCell
        let (tag, cs1) ← cs0.takeBitsAsNatCellUnd 8
        if tag != 0xc0 then
          throw .cellUnd
        let (hmeTag, cs2) ← cs1.takeBitsAsNatCellUnd 1
        if hmeTag = 0 then
          return none
        let (root, _rest) ← cs2.takeRefCell
        let val? ← dictLookup (some root) codeHashBits
        match val? with
        | none => return none
        | some valSlice =>
            let (vtag, s1) ← valSlice.takeBitsAsNatCellUnd 8
            if vtag != 0xb0 then
              throw .cellUnd
            let (gas, _s2) ← s1.takeBitsAsNatCellUnd 64
            return some gas : Except Excno (Option Nat)) with
      | .ok v => v
      | .error _ => none

    match si.config_precompiled_contracts_boc with
    | none => .null
    | some boc =>
        match decodeBytes boc with
        | .error _ => .null
        | .ok bs =>
            match stdBocDeserialize bs with
            | .error _ => .null
            | .ok cfgCell =>
                match lookupGasUsage? cfgCell with
                | some g => .int (.num (Int.ofNat g))
                | none => .null
  let mcFwdPricesVal : Value :=
    match si.config_mc_fwd_prices_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null
  let fwdPricesVal : Value :=
    match si.config_fwd_prices_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let storagePricesVal : Value :=
    -- `UNPACKEDCONFIGTUPLE[0]` is the current `StoragePrices` entry selected by `now` (not the whole dict),
    -- see C++ `Config::get_unpacked_config_tuple` (mc-config.cpp).
    let selectCurrentStoragePrices (root : Cell) : Value :=
      let hintBits : BitString := natToBits si.now.toNat 32
      match dictNearestWithCells (some root) hintBits false true false with
      | .ok (some (valSlice, _), _) =>
          -- `dictNearestWithCells` returns a slice into the dict payload; trim it to a standalone cell.
          .slice (Slice.ofCell valSlice.toCellRemaining)
      | .ok (none, _) => .null
      | .error _ => .null
    match si.config_storage_prices_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c =>
                if c.bits.isEmpty && c.refs.isEmpty then
                  .null
                else
                  selectCurrentStoragePrices c
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let globalIdVal : Value :=
    match si.config_global_id_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let mcGasPricesVal : Value :=
    match si.config_mc_gas_prices_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let gasPricesVal : Value :=
    match si.config_gas_prices_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null

  let sizeLimitsVal : Value :=
    match si.config_size_limits_boc with
    | some boc =>
        match decodeBytes boc with
        | .ok bs =>
            match stdBocDeserialize bs with
            | .ok c => .slice (Slice.ofCell c)
            | .error _ => .null
        | .error _ => .null
    | none => .null

  -- `Transaction::prepare_vm_c7` stores the unpacked config tuple at params[14] for global_version >= 6.
  -- Include the config slices needed for common fee opcodes (ConfigParams 18-21,24-25).
  let unpacked0 : Array Value := #[]
  let unpacked1 := tupleSetExtend unpacked0 0 storagePricesVal
  let unpacked2 := tupleSetExtend unpacked1 1 globalIdVal
  let unpacked3 := tupleSetExtend unpacked2 2 mcGasPricesVal
  let unpacked4 := tupleSetExtend unpacked3 3 gasPricesVal
  let unpacked5 := tupleSetExtend unpacked4 4 mcFwdPricesVal
  let unpacked6 := tupleSetExtend unpacked5 5 fwdPricesVal
  let unpacked7 := tupleSetExtend unpacked6 6 sizeLimitsVal

  let params10 := tupleSetExtend params9 14 (.tuple unpacked7) -- UNPACKEDCONFIGTUPLE
  let params11 := tupleSetExtend params10 15 (.int (.num si.due_payment)) -- DUEPAYMENT
  let params12 := tupleSetExtend params11 16 precompiledGasUsageVal -- GETPRECOMPILEDGAS (Maybe Integer)
  let params13 := tupleSetExtend params12 17 inMsgParamsVal -- INMSGPARAMS (TVM global_version >= 11)
  #[.tuple params13]

def runTestCase (cfg : RunConfig) (tc : TestCase) : IO TestResult := do
  let expectedExitRaw : Int := tc.expected.exit_code
  let expectedExit : Int :=
    if expectedExitRaw < 0 then
      -- Some fixture sets store `vm.run()`-style exit codes (-1 for success).
      -- Normalize to blockchain `compute_exit_code` (like `cp.exit_code = ~vm.run()`).
      ~~~ expectedExitRaw
    else
      expectedExitRaw

  let mkErr (msg : String) : TestResult :=
    { tx_hash := tc.tx_hash
      status := .error
      expected_exit_code := expectedExit
      expected_gas_used := tc.expected.gas_used
      error := some msg }

  let mkSkip (msg : String) : TestResult :=
    { tx_hash := tc.tx_hash
      status := .skip
      expected_exit_code := expectedExit
      expected_gas_used := tc.expected.gas_used
      error := some msg }

  let isUnsupportedBocError (msg : String) : Bool :=
    let has (sub : String) : Bool := (msg.splitOn sub).length > 1
    has "special/exotic cells not supported" ||
    has "non-zero level mask not supported" ||
    has "absent cells not supported"

  match decodeBytes tc.code_boc with
  | .error e => return mkErr s!"code_boc decode: {e}"
  | .ok codeBytes =>
      match decodeBytes tc.data_boc with
      | .error e => return mkErr s!"data_boc decode: {e}"
      | .ok dataBytes =>
          match stdBocDeserialize codeBytes with
          | .error e =>
              let msg := s!"code_boc parse: {e}"
              if cfg.skipUnsupported && isUnsupportedBocError (toString e) then
                return mkSkip msg
              else
                return mkErr msg
          | .ok codeCell =>
              match stdBocDeserialize dataBytes with
              | .error e =>
                  let msg := s!"data_boc parse: {e}"
                  if cfg.skipUnsupported && isUnsupportedBocError (toString e) then
                    return mkSkip msg
                  else
                    return mkErr msg
              | .ok dataCell =>
                  match buildInitStack tc.stack_init with
                  | .error e =>
                      let msg := s!"stack_init: {e}"
                      if cfg.skipUnsupported && isUnsupportedBocError e then
                        return mkSkip msg
                      else
                        return mkErr msg
                  | .ok initStack =>
                      let myCodeCellForC7 : Cell :=
                        match tc.mycode_boc? with
                        | none => codeCell
                        | some boc =>
                            match decodeBytes boc with
                            | .error _ => codeCell
                            | .ok bs =>
                                match stdBocDeserialize bs with
                                | .ok c => c
                                | .error _ => codeCell
                      let initC7 : Array Value := defaultInitC7 tc.stack_init codeCell myCodeCellForC7

                      let gasLimitInit : Int := tc.expected.gas_limit.getD cfg.gasLimit
                      let gasMax0 : Int := tc.expected.gas_max.getD cfg.gasLimit
                      let gasMaxInit : Int := if gasMax0 < gasLimitInit then gasLimitInit else gasMax0
                      let gasCreditInit : Int := tc.expected.gas_credit.getD 0
                      -- Compute-phase VM in TON is created with `flags=1` (same_c3), i.e. `c3 := OrdCont(code, cp)`
                      -- so that CALLDICT/JMPDICT re-enter the root code dispatcher.
                      let base0 := VmState.initial codeCell gasLimitInit gasMaxInit gasCreditInit
                      let base : VmState := { base0 with regs := { base0.regs with c3 := base0.cc } }
                      let st0 : VmState :=
                        { base with
                          stack := initStack
                          regs := { base.regs with c4 := dataCell, c7 := initC7 } }

                      let precompiledGasUsage? : Option Int :=
                        match initC7.get? 0 with
                        | some (.tuple params) =>
                            match params.get? 16 with
                            | some (.int (.num n)) => some n
                            | _ => none
                        | _ => none

                      match precompiledGasUsage? with
                      | some g =>
                          return mkSkip s!"precompiled contract detected (config_param_45 gas={g}); skipping"
                      | none => pure ()

                      let mkBase (exitCode : Int) (stF : VmState) : TestResult :=
                        -- `VmState.run*` returns bitwise-complemented exit codes (like C++ `vm.run()`).
                        -- Blockchain `compute_exit_code` is the uncomplemented one (like C++ `cp.exit_code = ~vm.run()`).
                        let actualExit : Int := ~~~ exitCode
                        -- Fixtures use Fift `runvmx` GAS output, which reports `gas_consumed()`
                        -- (not blockchain `compute_phase.gas_used = min(gas_consumed, gas_limit)`).
                        let gasUsed : Int := stF.gas.gasConsumed
                        let isUnsupported := actualExit = Excno.invOpcode.toInt
                        let mismatches0 : Array String := #[]
                        let expExitStr : String :=
                          if expectedExitRaw < 0 then
                            s!"{expectedExit} (normalized from {expectedExitRaw})"
                          else
                            s!"{expectedExit}"
                        let mismatches1 :=
                          if actualExit ≠ expectedExit then
                            mismatches0.push s!"exit_code expected={expExitStr} actual={actualExit}"
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
                          expected_exit_code := expectedExit
                          actual_exit_code := some actualExit
                          expected_gas_used := tc.expected.gas_used
                          actual_gas_used := some gasUsed
                          error := err }

                      let attachExpectedCells (base : TestResult) (stF : VmState) : IO TestResult := do
                        if base.status == .skip then
                          return base
                        let mut mismatches : Array String := #[]

                        -- Always compare the VM registers as-is after execution (no "committed state" gating).
                        let finalC4 : Cell := stF.regs.c4
                        let finalC5 : Cell := stF.regs.c5

                        let bytesToHex (bs : Array UInt8) : String :=
                          "0x" ++ String.intercalate "" (bs.toList.map (fun b => natToHexPad b.toNat 2))
                        let cellHashHex (c : Cell) : String :=
                          bytesToHex (Cell.hashBytes c)
                        let describeValue (v : Value) : String :=
                          match v with
                          | .null => "null"
                          | .int .nan => "nan"
                          | .int (.num n) => s!"int({n})"
                          | .cell c => s!"cell({cellHashHex c})"
                          | .slice s => s!"slice({cellHashHex s.cell},bitPos={s.bitPos},refPos={s.refPos})"
                          | .builder b => s!"builder(bits={b.bits.size},refs={b.refs.size})"
                          | .tuple t => s!"tuple(len={t.size})"
                          | .cont _ => "cont"

                        match tc.expected.c4_boc with
                        | some s =>
                            match decodeBytes s with
                            | .error e => mismatches := mismatches.push s!"expected.c4_boc decode: {e}"
                            | .ok bytes =>
                                match stdBocDeserialize bytes with
                                | .error e => mismatches := mismatches.push s!"expected.c4_boc parse: {e}"
                                | .ok exp =>
                                    if !(finalC4 == exp) then
                                      mismatches :=
                                        mismatches.push
                                          s!"c4 mismatch expected={cellHashHex exp} actual={cellHashHex finalC4}"
                        | none => pure ()

                        match tc.expected.c5_boc with
                        | some s =>
                            match decodeBytes s with
                            | .error e => mismatches := mismatches.push s!"expected.c5_boc decode: {e}"
                            | .ok bytes =>
                                match stdBocDeserialize bytes with
                                | .error e => mismatches := mismatches.push s!"expected.c5_boc parse: {e}"
                                | .ok exp =>
                                    if !(finalC5 == exp) then
                                      mismatches :=
                                        mismatches.push
                                          s!"c5 mismatch expected={cellHashHex exp} actual={cellHashHex finalC5}"
                        | none => pure ()

                        match tc.expected.c7 with
                        | some expC7 =>
                            match expC7.toValue with
                            | .error e => mismatches := mismatches.push s!"expected.c7: {e}"
                            | .ok v =>
                                match v with
                                | .tuple items =>
                                    if stF.regs.c7.size != items.size then
                                      mismatches :=
                                        mismatches.push
                                          s!"c7 mismatch (size expected={items.size} actual={stF.regs.c7.size})"
                                    else if !(arrayBeqBy stF.regs.c7 items valueEqNormalized) then
                                      let firstMismatch? : Option Nat :=
                                        Id.run do
                                          let mut m : Option Nat := none
                                          for i in [0:items.size] do
                                            if m.isNone then
                                              if !valueEqNormalized (stF.regs.c7[i]!) (items[i]!) then
                                                m := some i
                                          return m
                                      match firstMismatch? with
                                      | some i =>
                                          let exp := items[i]!
                                          let act := stF.regs.c7[i]!
                                          match firstValueMismatch exp act with
                                          | some (path, leafE, leafA) =>
                                              let pathStr :=
                                                match path with
                                                | [] => "<root>"
                                                | _ =>
                                                    let parts := path.map toString
                                                    String.intercalate "." parts
                                              mismatches :=
                                                mismatches.push
                                                  s!"c7 mismatch at idx={i} path={pathStr} expected={describeValue leafE} actual={describeValue leafA}"
                                          | none =>
                                              mismatches :=
                                                mismatches.push
                                                  s!"c7 mismatch at idx={i} expected={describeValue exp} actual={describeValue act}"
                                      | none =>
                                          mismatches := mismatches.push "c7 mismatch"
                                | _ =>
                                    mismatches := mismatches.push "expected.c7: expected tuple"
                        | none =>
                            pure ()

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
                        let (res, t, wrapped) := VmState.runTrace nativeHost cfg.fuel st0 cfg.traceMax
                        match res with
                        | .continue _ =>
                            return {
                              tx_hash := tc.tx_hash
                              status := .fail
                              expected_exit_code := expectedExit
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
                        match VmState.run nativeHost cfg.fuel st0 with
                        | .continue _ =>
                            return {
                              tx_hash := tc.tx_hash
                              status := .fail
                              expected_exit_code := expectedExit
                              expected_gas_used := tc.expected.gas_used
                              error := some "fuel exhausted"
                            }
                        | .halt exitCode stF =>
                            let base := mkBase exitCode stF
                            let base ← attachExpectedCells base stF

                            if cfg.traceFailures && base.status ≠ .pass then
                              let (_, t, wrapped) := VmState.runTrace nativeHost cfg.fuel st0 cfg.traceMax
                              return { base with trace := some t, trace_truncated := some wrapped }
                            else
                              return base

end TvmLean
