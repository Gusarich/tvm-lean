import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTSWITCH

/-!
INSTRUCTION: PFXDICTSWITCH

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch behavior.
   - `execInstrDictExt` handles only `.dictExt (.pfxSwitch ...)`.
   - non-matching instructions must continue via `next`.

2. [B2] Runtime arity/type checks.
   - handler requires at least one stack item (the key).
   - key must be slice (`popSlice`), else `.typeChk`.

3. [B3] 24-bit decoder family + inline ref constraints.
   - family prefix `0x3d2b` with 10-bit key_len.
   - decoding consumes 24 bits and requires exactly one inline reference.
   - missing ref/truncated stream returns `.invOpcode`.

4. [B4] Family boundary checks.
   - valid window is `0x3d2b000..0x3d2b3ff`.
   - neighbors `0x3d2afff` and `0x3d2c000` decode as `.invOpcode`.

5. [B5] Assembler validation.
   - `.dictExt` is rejected in `assembleCp0`, so `.dictExt (.pfxSwitch ...)` must be `.invOpcode`.

6. [B6] Runtime miss path.
   - when no prefix found, original key is pushed back (with stack preservation below it).

7. [B7] Runtime hit path.
   - matched keys trigger jump to value continuation.

8. [B8] Malformed dictionary errors.
   - malformed prefix dictionaries propagate dictionary errors (`.dictErr` etc.).

9. [B9] Gas behavior.
   - fixed exact base budget; exact and exact-1 outcomes.

TOTAL BRANCHES: 9

Any branch not directly represented in oracle is expected to be explored by fuzz.
-/

private def suiteId : InstrId :=
  { name := "PFXDICTSWITCH" }

private def instrPfxSet : Instr :=
  .dictExt (.pfxSet .set)

private def pfxSwitchPrefix : Nat := 0x3d2b

private def pfxSwitchBase : Nat :=
  pfxSwitchPrefix <<< 10

private def rawSwitch24 (keyLen : Nat) (dictCell : Cell) (tail : BitString := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + (keyLen &&& 0x3ff)) 24 ++ tail) #[dictCell]

private def rawSwitch24NoRef (keyLen : Nat) (tail : BitString := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + (keyLen &&& 0x3ff)) 24 ++ tail) #[]

private def rawLowerInvalid : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase - 1) 24) #[]

private def rawUpperInvalid : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + 0x400) 24) #[]

private def rawTruncated23 : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + 19) 23) #[]

private def rawTruncated8 : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + 20) 8) #[]

private def malformedPrefixRoot : Cell :=
  Cell.mkOrdinary (natToBits 0 2) #[]

private def mkPfxDict (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let bits : BitString := pair.1
      let value : Slice := pair.2
      let n : Nat := bits.size
      let dictVal : Value :=
        match root with
        | none => .null
        | some c => .cell c
      let stack : Array Value := #[.slice value, .slice (mkSliceFromBits bits), dictVal, intV (Int.ofNat n)]
      match runHandlerDirect execInstrDictExt instrPfxSet stack with
      | .ok #[.cell next, ok] =>
          if ok != intV (-1) then
            panic! s!"{label}: pfxSet returned ok={reprStr ok}"
          root := some next
      | .ok st =>
          panic! s!"{label}: pfxSet unexpected stack {reprStr st}"
      | .error e =>
          panic! s!"{label}: pfxSet failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: failed to build dictionary"

private def dict4MatchBits : BitString :=
  natToBits 0b1101 4

private def dict4MissBits : BitString :=
  natToBits 0b0011 4

private def dict4LongBits : BitString :=
  natToBits 0b11010010 8

private def dict4Value : Slice :=
  mkSliceFromBits (natToBits 0xA5A5 16)

private def dict0Value : Slice :=
  mkSliceFromBits (natToBits 0x5A5A 16)

private def pfxDict4Root : Cell :=
  mkPfxDict "pfx-switch/dict4" #[(dict4MatchBits, dict4Value)]

private def pfxDict0Root : Cell :=
  mkPfxDict "pfx-switch/dict0" #[(#[], dict0Value)]

private def rawChain : Cell :=
  Cell.mkOrdinary (natToBits (pfxSwitchBase + 4) 24 ++ natToBits 0x5a 16) #[pfxDict4Root]

private def instrSwitch4 : Instr :=
  .dictExt (.pfxSwitch pfxDict4Root 4)

private def instrSwitch0 : Instr :=
  .dictExt (.pfxSwitch pfxDict0Root 0)

private def instrSwitch1023 : Instr :=
  .dictExt (.pfxSwitch pfxDict4Root 1023)

private def instrSwitchMalformed : Instr :=
  .dictExt (.pfxSwitch malformedPrefixRoot 4)

private def dispatchSentinel : Int := 12_345

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def sentinelC0 : Continuation := .quit 99

private def regsWithSentinelC0 : Regs :=
  { Regs.initial with c0 := sentinelC0 }

private def keyMatchSlice : Slice := mkSliceFromBits dict4MatchBits
private def keyMissSlice : Slice := mkSliceFromBits dict4MissBits
private def keyLongSlice : Slice := mkSliceFromBits dict4LongBits

private def runDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def runDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runRaw
    (instr : Instr)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrDictExt instr (pure ())).run st0

private def expectRawOk
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (res : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected error {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectStack (label : String) (expected : Array Value) (st : VmState) : IO Unit := do
  if st.stack == expected then
    pure ()
  else
    throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st.stack}")

private def expectJumpTransfer
    (label : String)
    (target : Slice)
    (expectedC0 : Continuation)
    (st : VmState) : IO Unit := do
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code.toCellRemaining != target.toCellRemaining then
        throw (IO.userError s!"{label}: expected jump target {reprStr target}, got {reprStr code}")
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr st.cc}")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0 {reprStr expectedC0}, got {reprStr st.regs.c0}")

private def expectDecodeInv (label : String) (cell : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell cell) with
  | .ok (i, _, _) => throw (IO.userError s!"{label}: expected invOpcode, got {reprStr i}")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectDecodeOk (label : String) (cell : Cell) (expected : Instr) : IO Unit := do
  let _ ← expectDecodeStep label (Slice.ofCell cell) expected 24
  pure ()

private def expectAssembleInv (label : String) (instr : Instr) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got success")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def pfxSwitchGas : Int := computeExactGasBudget instrSwitch4
private def pfxSwitchGasMinusOne : Int := computeExactGasBudgetMinusOne instrSwitch4

private def pfxSwitchGasLimitsExact : OracleGasLimits :=
  oracleGasLimitsExact pfxSwitchGas

private def pfxSwitchGasLimitsExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne pfxSwitchGasMinusOne

private def mkCase
    (name : String)
    (stack : Array Value := #[])
    (program : Array Instr := #[instrSwitch4])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (stack : Array Value := #[])
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genPFXDICTSWITCH (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/0"
    else if shape = 1 then
      mkCase "fuzz/type/not-slice" #[.int (.num 7)]
    else if shape = 2 then
      mkCase "fuzz/type/null" #[.null]
    else if shape = 3 then
      mkCase "fuzz/type/builder" #[.builder Builder.empty]
    else if shape = 4 then
      mkCase "fuzz/miss/0" #[.slice keyMissSlice]
    else if shape = 5 then
      mkCase "fuzz/miss/with-tail" #[intV 42, .slice keyMissSlice]
    else if shape = 6 then
      mkRawCase "fuzz/raw/miss" #[.slice keyMissSlice] (rawSwitch24 4 pfxDict4Root)
    else if shape = 7 then
      mkRawCase "fuzz/raw/miss-with-tail" #[intV 7, .slice keyMissSlice] (rawSwitch24 4 pfxDict4Root)
    else if shape = 8 then
      mkRawCase "fuzz/raw/hit" #[.slice keyMatchSlice] (rawSwitch24 4 pfxDict4Root)
    else if shape = 9 then
      mkRawCase "fuzz/raw/hit-with-tail" #[intV 1, .slice keyMatchSlice] (rawSwitch24 4 pfxDict4Root)
    else if shape = 10 then
      mkRawCase "fuzz/raw/keylen-0" #[.slice keyLongSlice] (rawSwitch24 0 pfxDict0Root)
    else if shape = 11 then
      mkRawCase "fuzz/raw/keylen-1023" #[.slice keyLongSlice] (rawSwitch24 1023 pfxDict4Root)
    else if shape = 12 then
      mkRawCase "fuzz/raw/malformed-root" #[.slice keyMissSlice] (rawSwitch24 4 malformedPrefixRoot)
    else if shape = 13 then
      mkRawCase "fuzz/raw/truncated23" #[] rawTruncated23
    else if shape = 14 then
      mkRawCase "fuzz/raw/truncated8" #[] rawTruncated8
    else if shape = 15 then
      mkRawCase "fuzz/raw/gas-exact" #[.slice keyMissSlice] (rawSwitch24 4 pfxDict4Root) pfxSwitchGasLimitsExact
    else
      mkRawCase "fuzz/raw/gas-exact-minus-one" #[.slice keyMissSlice] (rawSwitch24 4 pfxDict4Root) pfxSwitchGasLimitsExactMinusOne
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/non-match" -- [B1]
      run := do
        let st := runDispatchFallback .add #[.slice keyMatchSlice]
        expectOkStack "unit/dispatch/non-match" st #[.slice keyMatchSlice, intV dispatchSentinel] },
    { name := "unit/dispatch/match-miss" -- [B1][B6]
      run := do
        let st := runDispatchFallback instrSwitch4 #[.slice keyMissSlice]
        expectOkStack "unit/dispatch/match-miss" st #[.slice keyMissSlice] },
    { name := "unit/underflow" -- [B2]
      run := do
        expectErr "unit/underflow" (runDirect instrSwitch4 #[]) .stkUnd },
    { name := "unit/type-key" -- [B2]
      run := do
        expectErr "unit/type-key" (runDirect instrSwitch4 #[.int (.num 7)]) .typeChk },
    { name := "unit/miss-with-tail" -- [B6]
      run := do
        expectOkStack
          "unit/miss-with-tail"
          (runDirect instrSwitch4 #[intV 7, .slice keyMissSlice])
          #[intV 7, .slice keyMissSlice] },
    { name := "unit/malformed-root" -- [B8]
      run := do
        expectErr "unit/malformed-root" (runDirect instrSwitchMalformed #[.slice keyMissSlice]) .dictErr },
    { name := "unit/raw/miss" -- [B6]
      run := do
        let st ← expectRawOk
          "unit/raw/miss"
          (runRaw instrSwitch4 #[.slice keyMissSlice] regsWithSentinelC0 defaultCc)
        expectStack "unit/raw/miss" #[.slice keyMissSlice] st },
    { name := "unit/raw/hit-jump" -- [B7]
      run := do
        let st ← expectRawOk
          "unit/raw/hit-jump"
          (runRaw instrSwitch4 #[.slice keyMatchSlice] regsWithSentinelC0 defaultCc)
        match st.stack with
        | #[.slice pfx, .slice rest] =>
            if pfx.toCellRemaining.bits != dict4MatchBits then
              throw (IO.userError s!"unit/raw/hit-jump: bad prefix {pfx.toCellRemaining.bits}")
            if rest.bitsRemaining != 0 then
              throw (IO.userError s!"unit/raw/hit-jump: expected empty rest, got {rest.toCellRemaining.bits}")
        | _ =>
            throw (IO.userError s!"unit/raw/hit-jump: unexpected stack {reprStr st.stack}")
        expectJumpTransfer "unit/raw/hit-jump" dict4Value sentinelC0 st },
    { name := "unit/raw/hit-jump-with-tail" -- [B7]
      run := do
        let st ← expectRawOk
          "unit/raw/hit-jump-with-tail"
          (runRaw instrSwitch4 #[intV 7, .slice keyMatchSlice] regsWithSentinelC0 defaultCc)
        match st.stack with
        | #[head, .slice pfx, .slice rest] =>
            if head != intV 7 then
              throw (IO.userError s!"unit/raw/hit-jump-with-tail: expected tail int 7, got {reprStr head}")
            if pfx.toCellRemaining.bits != dict4MatchBits then
              throw (IO.userError s!"unit/raw/hit-jump-with-tail: bad prefix {pfx.toCellRemaining.bits}")
            if rest.bitsRemaining != 0 then
              throw (IO.userError s!"unit/raw/hit-jump-with-tail: expected empty rest, got {rest.toCellRemaining.bits}")
        | _ =>
            throw (IO.userError s!"unit/raw/hit-jump-with-tail: unexpected stack {reprStr st.stack}")
        expectJumpTransfer "unit/raw/hit-jump-with-tail" dict4Value sentinelC0 st },
    { name := "unit/raw/malformed-root" -- [B8]
      run := do
        let _ ← expectRawErr
          "unit/raw/malformed-root"
          (runRaw instrSwitchMalformed #[.slice keyMissSlice])
          .dictErr
        pure () },
    { name := "unit/assemble" -- [B5]
      run := do
        expectAssembleInv "unit/assemble" instrSwitch4
        expectAssembleInv "unit/assemble/alt-key-len" instrSwitch1023
        expectAssembleInv "unit/assemble/malformed" instrSwitchMalformed },
    { name := "unit/decode/family" -- [B3][B4]
      run := do
        expectDecodeOk "unit/decode/target" (rawSwitch24 4 pfxDict4Root) instrSwitch4
        let _ ← expectDecodeStep "unit/decode/chain" (Slice.ofCell rawChain) instrSwitch4 24
        let _ ←
          expectDecodeStep
            "unit/decode/lower-neighbor"
            (Slice.ofCell rawLowerInvalid)
            (.dictExt (.pfxGet .getExec))
            16
        expectDecodeInv "unit/decode/upper" rawUpperInvalid
        match decodeCp0WithBits (Slice.ofCell rawTruncated23) with
        | .error _ => pure ()
        | .ok (i, bits, _) =>
            match i with
            | .dictExt (.pfxSwitch _ _) =>
                throw (IO.userError s!"unit/decode/truncated23: expected non-pfxSwitch, got {reprStr i}/{bits}")
            | _ => pure ()
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok (i, bits, _) =>
            match i with
            | .dictExt (.pfxSwitch _ _) =>
                throw (IO.userError s!"unit/decode/truncated8: expected non-pfxSwitch, got {reprStr i}/{bits}")
            | _ => pure ()
        expectDecodeInv "unit/decode/missing-ref" (rawSwitch24NoRef 4)
        pure () }
  ]
  oracle := #[
    mkCase "oracle/underflow" #[],
    mkCase "oracle/type-int" #[.int (.num 7)],
    mkCase "oracle/miss" #[.slice keyMissSlice],
    mkCase "oracle/miss-with-tail" #[intV 9, .slice keyMissSlice],
    mkRawCase "oracle/raw/miss" #[.slice keyMissSlice] (rawSwitch24 4 pfxDict4Root),
    mkRawCase "oracle/raw/hit" #[.slice keyMatchSlice] (rawSwitch24 4 pfxDict4Root),
    mkRawCase "oracle/raw/hit-long-key" #[.slice keyLongSlice] (rawSwitch24 4 pfxDict4Root),
    mkRawCase "oracle/raw/keylen-0" #[.slice keyLongSlice] (rawSwitch24 0 pfxDict0Root),
    mkRawCase "oracle/raw/keylen-1023" #[.slice keyLongSlice] (rawSwitch24 1023 pfxDict4Root),
    mkRawCase "oracle/raw/malformed-root" #[.slice keyMissSlice] (rawSwitch24 4 malformedPrefixRoot),
    mkRawCase "oracle/raw/lower-invalid" #[] rawLowerInvalid,
    mkRawCase "oracle/raw/upper-invalid" #[] rawUpperInvalid,
    mkRawCase "oracle/raw/truncated23" #[] rawTruncated23,
    mkRawCase "oracle/raw/truncated8" #[] rawTruncated8,
    mkRawCase "oracle/raw/missing-ref" #[] (rawSwitch24NoRef 4),
    mkRawCase "oracle/raw/chain" #[.slice keyMissSlice] rawChain,
    mkCase "oracle/gas/exact"
      #[.slice keyMissSlice]
      (program := #[.pushInt (.num pfxSwitchGas), .tonEnvOp .setGasLimit, instrSwitch4])
      pfxSwitchGasLimitsExact,
    mkCase "oracle/gas/exact-minus-one"
      #[.slice keyMissSlice]
      (program := #[.pushInt (.num pfxSwitchGasMinusOne), .tonEnvOp .setGasLimit, instrSwitch4])
      pfxSwitchGasLimitsExactMinusOne,
    mkCase "oracle/raw-assemble-invariant" #[.slice keyMatchSlice] (program := #[instrSwitch4]) (gasLimits := {})
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPFXDICTSWITCH }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTSWITCH
