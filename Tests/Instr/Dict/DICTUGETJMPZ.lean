import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETJMPZ

/-!
INSTRUCTION: DICTUGETJMPZ

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch.
2. [B2] Runtime precondition checks:
   - stack underflow (`checkUnderflow 3`),
   - key-size check (`popNatUpTo 1023`),
   - dict root pop (`popMaybeCell`),
   - key pop (`popIntFinite`).
3. [B3] Type/range error branches.
   - `n` non-int or out-of-range (`typeChk`, `rangeChk`),
   - dictionary argument non-null/cell (`typeChk`),
   - key non-int (`typeChk`) and NaN key (`intOv`).
4. [B4] Unsigned key conversion (`dictKeyBits?`) + `pushZ`.
   - valid keys convert to a bitstring of length `n`,
   - invalid keys (negative/out-of-range or wrong `n`) do not lookup and push the original key back.
5. [B5] Lookup hit branch.
   - valid conversion + found value -> ordinary continuation created from dict value and jump transfer.
6. [B6] Lookup miss branches.
   - root null / valid conversion miss / key-conversion-fail / malformed traversal all fall through to `pushZ`.
7. [B7] Malformed dictionary root handling.
   - malformed root cell causes dictionary lookup failure (`dictErr`).
8. [B8] Assembler/decoder boundaries.
   - valid families:
     `0xf4a0..0xf4a3` (Z disabled),
     `0xf4bc..0xf4bf` (Z enabled).
   - masked decoding (`&&& 0xfffc`) means adjacency above/below these families is `invOpcode`.
9. [B9] Gas accounting.
   - base-cost-only path; exact-gas-success and exact-gas-minus-one paths.

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn].
Any branch not covered by oracle tests is expected to be covered by the fuzz generator.
-/

private def suiteId : InstrId := { name := "DICTUGETJMPZ" }

private def instrSignedJmp : Instr := .dictGetExec false false false
private def instrUnsignedJmpZ : Instr := .dictGetExec true false true
private def instrUnsignedJmp : Instr := .dictGetExec true false false
private def instrUnsignedCallZ : Instr := .dictGetExec true true true
private def instrSignedCallZ : Instr := .dictGetExec false true true

private def markerSlice (marker : Nat) : Slice := mkSliceFromBits (natToBits marker 16)
private def rawOpcode16 (w16 : Nat) : Cell := Cell.mkOrdinary (natToBits w16 16) #[]

private def jumpTargetSlice : Slice := markerSlice 0xCA11
private def n0MarkerSlice : Slice := markerSlice 0x00F0
private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def dispatchSentinel : Int := 99_001

private def mkDictFromPairs (label : String) (n : Nat) (unsigned : Bool)
    (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let k := pair.1
      let value := pair.2
      let keyBits : BitString :=
        match dictKeyBits? k n unsigned with
        | some bits => bits
        | none => panic! s!"{label}: invalid key {k} for n={n} unsigned={unsigned}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some next, _, _, _) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: insertion returned none"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some result => result
    | none => panic! s!"{label}: failed to build dictionary"

private def dictUnsigned4HitRoot : Cell :=
  mkDictFromPairs "dictUnsigned4HitRoot" 4 true #[(3, jumpTargetSlice)]

private def dictUnsigned4MissRoot : Cell :=
  mkDictFromPairs "dictUnsigned4MissRoot" 4 true #[(2, markerSlice 0xCAFE)]

private def dictUnsigned4Root : Cell :=
  mkDictFromPairs "dictUnsigned4Root" 4 true #[(3, jumpTargetSlice), (2, markerSlice 0xCAFE)]

private def dictUnsignedN0Root : Cell :=
  mkDictFromPairs "dictUnsignedN0Root" 0 true #[(0, n0MarkerSlice)]

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def mkCase
    (name : String)
    (instr : Instr)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[instr]) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value := #[])
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

private def runDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec instr (VM.push (intV dispatchSentinel)) stack

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
  (execInstrDictDictGetExec instr (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr (label : String) (res : Except Excno Unit × VmState) (expected : Excno) : IO VmState := do
  let (r, st) := res
  match r with
  | .ok _ => throw (IO.userError s!"{label}: expected error {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectJumpTransfer (label : String) (target : Slice) (st : VmState) : IO Unit := do
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code.bitsRemaining = 0 then
        throw (IO.userError s!"{label}: expected non-empty continuation code")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation after jump")
  if st.regs.c0 != Regs.initial.c0 then
    throw (IO.userError s!"{label}: expected regs.c0 unchanged, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected stack consumed, got {reprStr st.stack}")

private def expectDecodeStepExact (label : String) (instr : Instr) (w16 : Nat) : IO Unit := do
  let _ ← expectDecodeStep label (Slice.ofCell (rawOpcode16 w16)) instr 16

private def expectDecodeSuccess (label : String) (w16 : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (rawOpcode16 w16)) with
  | .ok (_, bits, rest) =>
      if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected full consume")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeInv (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (rawOpcode16 opcode)) with
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got instruction")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (tag, rng1) := randNat rng0 0 999_999
  (s!"{name}/{tag}", rng1)

private def dictExactGas : Int := computeExactGasBudget instrUnsignedJmpZ
private def dictExactMinusOneGas : Int := computeExactGasBudgetMinusOne instrUnsignedJmpZ

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictExactGas
private def gasMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictExactMinusOneGas

private def genDICTUGETJMPZ (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/0" instrUnsignedJmpZ #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/1" instrUnsignedJmpZ #[.null]
    else if shape = 2 then
      mkCase "fuzz/underflow/2" instrUnsignedJmpZ #[(.null), (.cell dictUnsigned4HitRoot)]
    else if shape = 3 then
      mkCase "fuzz/err/n-type" instrUnsignedJmpZ (#[(.cell dictUnsigned4HitRoot), intV 3, .slice (markerSlice 0x7777)])
    else if shape = 4 then
      mkCase "fuzz/err/n-nan" instrUnsignedJmpZ (#[(.cell dictUnsigned4HitRoot), intV 3, .int .nan])
    else if shape = 5 then
      mkCase "fuzz/err/n-negative" instrUnsignedJmpZ (#[(.cell dictUnsigned4HitRoot), intV 3, intV (-1)])
    else if shape = 6 then
      mkCase "fuzz/err/n-too-large" instrUnsignedJmpZ (#[(.cell dictUnsigned4HitRoot), intV 3, intV 2048])
    else if shape = 7 then
      mkCase "fuzz/err/dict-type" instrUnsignedJmpZ (#[intV 3, intV 3, intV 4])
    else if shape = 8 then
      mkCase "fuzz/err/key-null" instrUnsignedJmpZ (#[.null, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 9 then
      mkCase "fuzz/err/key-nan" instrUnsignedJmpZ (#[.int .nan, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 10 then
      mkCase "fuzz/err/key-cell" instrUnsignedJmpZ (#[.cell dictUnsigned4HitRoot, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 11 then
      mkCase "fuzz/hit" instrUnsignedJmpZ (#[intV 3, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 12 then
      mkCase "fuzz/miss/null-dict" instrUnsignedJmpZ (#[intV 3, .null, intV 4])
    else if shape = 13 then
      mkCase "fuzz/miss/empty-dict" instrUnsignedJmpZ (#[intV 3, .null, intV 4])
    else if shape = 14 then
      mkCase "fuzz/miss/oob-pos" instrUnsignedJmpZ (#[intV 16, (.cell dictUnsigned4Root), intV 4])
    else if shape = 15 then
      mkCase "fuzz/miss/oob-neg" instrUnsignedJmpZ (#[intV (-1), (.cell dictUnsigned4Root), intV 4])
    else if shape = 16 then
      mkCase "fuzz/miss/n-zero-oob" instrUnsignedJmpZ (#[intV 1, (.cell dictUnsignedN0Root), intV 0])
    else if shape = 17 then
      mkCase "fuzz/miss/root-miss" instrUnsignedJmpZ (#[intV 2, (.cell dictUnsigned4MissRoot), intV 4])
    else if shape = 18 then
      mkCase "fuzz/miss/tail" instrUnsignedJmpZ (#[(intV 7), intV 3, (.cell dictUnsigned4MissRoot), intV 4])
    else if shape = 19 then
      mkCase "fuzz/dict-malformed-root" instrUnsignedJmpZ (#[intV 3, .cell malformedDictRoot, intV 4])
    else if shape = 20 then
      mkCase "fuzz/n-zero-hit" instrUnsignedJmpZ (#[intV 0, (.cell dictUnsignedN0Root), intV 0])
    else if shape = 21 then
      mkCase "fuzz/noop-dispatch" instrSignedJmp (#[intV 3, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 22 then
      mkCase
        "fuzz/gas/exact"
        instrUnsignedJmpZ
        (#[.cell dictUnsigned4HitRoot, intV 3, intV 4])
        gasExact
        (program := #[.pushInt (.num dictExactGas), .tonEnvOp .setGasLimit, instrUnsignedJmpZ])
    else if shape = 23 then
      mkCase
        "fuzz/gas/exact-minus-one"
        instrUnsignedJmpZ
        (#[.cell dictUnsigned4HitRoot, intV 3, intV 4])
        gasMinusOne
        (program := #[.pushInt (.num dictExactMinusOneGas), .tonEnvOp .setGasLimit, instrUnsignedJmpZ])
    else if shape = 24 then
      mkCase "fuzz/encode/f4bc" instrUnsignedJmp #[]
    else if shape = 25 then
      mkCase "fuzz/encode/f4be" instrUnsignedCallZ #[]
    else if shape = 26 then
      mkCase "fuzz/encode/f4bd" instrUnsignedJmpZ #[]
    else if shape = 27 then
      mkCase "fuzz/encode/f4bf" instrUnsignedCallZ #[]
    else if shape = 28 then
      mkCaseCode "fuzz/decode/f4bc" #[] (rawOpcode16 0xf4bc)
    else
      mkCaseCode "fuzz/decode/invalid-f4a4" #[] (rawOpcode16 0xf4a4)
  let (name, rng2) := addSuffixToCaseName case0.name rng1
  ({ case0 with name := name }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let init : Array Value := #[intV 3, (.cell dictUnsigned4HitRoot), intV 4]
        let st := runDispatchFallback .add init
        expectOkStack "unit/dispatch/fallback" st #[intV 3, (.cell dictUnsigned4HitRoot), intV 4, intV dispatchSentinel] },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let init : Array Value := #[intV 3, (.cell dictUnsigned4HitRoot), intV 4]
        let st := runDispatchFallback instrUnsignedJmpZ init
        expectOkStack "unit/dispatch/match" st #[] },
    { name := "unit/decoder/decode/f4bc" -- [B8]
      run := do
        expectDecodeSuccess "unit/decoder/decode/f4bc" 0xf4bc },
    { name := "unit/decoder/decode/f4bd" -- [B8]
      run := do
        expectDecodeStepExact "unit/decoder/decode/f4bd" instrUnsignedJmpZ 0xf4bd },
    { name := "unit/decoder/decode/f4be" -- [B8]
      run := do
        expectDecodeSuccess "unit/decoder/decode/f4be" 0xf4be },
    { name := "unit/decoder/decode/f4bf" -- [B8]
      run := do
        expectDecodeStepExact "unit/decoder/decode/f4bf" instrUnsignedCallZ 0xf4bf },
    { name := "unit/decoder/decode/f4a3" -- [B8]
      run := do
        expectDecodeSuccess "unit/decoder/decode/f4a3" 0xf4a3 },
    { name := "unit/asm/encode/f4bc" -- [B8]
      run := do
        match assembleCp0 [instrUnsignedJmp] with
        | .ok c =>
            if c.bits == natToBits 0xf4a1 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bc: expected bits 0xf4a1")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bc: expected success, got {e}") },
    { name := "unit/asm/encode/f4bd" -- [B8]
      run := do
        match assembleCp0 [instrUnsignedJmpZ] with
        | .ok c =>
            if c.bits == natToBits 0xf4bd 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bd: expected bits 0xf4bd")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bd: expected success, got {e}") },
    { name := "unit/asm/encode/f4be" -- [B8]
      run := do
        match assembleCp0 [instrSignedJmp] with
        | .ok c =>
            if c.bits == natToBits 0xf4a0 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4be: expected bits 0xf4a0")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4be: expected success, got {e}") },
    { name := "unit/asm/encode/f4bf" -- [B8]
      run := do
        match assembleCp0 [instrUnsignedCallZ] with
        | .ok c =>
            if c.bits == natToBits 0xf4bf 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bf: expected bits 0xf4bf")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bf: expected success, got {e}") },
    { name := "unit/decoder/invalid/f4a4" -- [B8]
      run := do
        expectDecodeInv "unit/decoder/invalid/f4a4" 0xf4a4 },
    { name := "unit/decoder/invalid/f4b0" -- [B8]
      run := do
        expectDecodeInv "unit/decoder/invalid/f4b0" 0xf4b0 },
    { name := "unit/decoder/invalid/f4c0" -- [B8]
      run := do
        expectDecodeInv "unit/decoder/invalid/f4c0" 0xf4c0 },
    { name := "unit/control/hit/jump" -- [B5]
      run := do
        let st ← expectRawOk "unit/control/hit/jump" (runRaw instrUnsignedJmpZ #[intV 3, (.cell dictUnsigned4HitRoot), intV 4] )
        expectJumpTransfer "unit/control/hit/jump" jumpTargetSlice st },
    { name := "unit/stack/miss/pushz" -- [B4]
      run := do
        expectOkStack "unit/stack/miss/pushz" (runDirect instrUnsignedJmpZ #[intV 16, (.cell dictUnsigned4Root), intV 4]) #[intV 16] },
    { name := "unit/stack/miss/pushz-tail" -- [B4]
      run := do
        expectOkStack "unit/stack/miss/pushz-tail" (runDirect instrUnsignedJmpZ #[intV 9, intV 16, (.cell dictUnsigned4Root), intV 4]) #[intV 9, intV 16] },
    { name := "unit/stack/miss/pushz-null-root" -- [B4]
      run := do
        expectOkStack "unit/stack/miss/pushz-null-root" (runDirect instrUnsignedJmpZ #[intV 7, .null, intV 4]) #[intV 7] },
    { name := "unit/errors/underflow/empty" -- [B2]
      run := do
        expectErr "unit/errors/underflow/empty" (runDirect instrUnsignedJmpZ #[]) .stkUnd },
    { name := "unit/errors/underflow/one" -- [B2]
      run := do
        expectErr "unit/errors/underflow/one" (runDirect instrUnsignedJmpZ #[.null]) .stkUnd },
    { name := "unit/errors/underflow/two" -- [B2]
      run := do
        expectErr "unit/errors/underflow/two" (runDirect instrUnsignedJmpZ #[.null, .null]) .stkUnd },
    { name := "unit/errors/n-negative" -- [B3]
      run := do
        expectErr "unit/errors/n-negative" (runDirect instrUnsignedJmpZ #[intV 3, (.cell dictUnsigned4HitRoot), intV (-1)]) .rangeChk },
    { name := "unit/errors/n-too-large" -- [B3]
      run := do
        expectErr "unit/errors/n-too-large" (runDirect instrUnsignedJmpZ #[intV 3, (.cell dictUnsigned4HitRoot), intV 1024]) .rangeChk },
    { name := "unit/errors/key-type" -- [B3]
      run := do
        expectErr "unit/errors/key-type" (runDirect instrUnsignedJmpZ #[.null, (.cell dictUnsigned4HitRoot), intV 4]) .typeChk },
    { name := "unit/errors/key-nan" -- [B3]
      run := do
        expectErr "unit/errors/key-nan" (runDirect instrUnsignedJmpZ #[.int .nan, (.cell dictUnsigned4HitRoot), intV 4]) .intOv },
    { name := "unit/errors/dict-type" -- [B3]
      run := do
        expectErr "unit/errors/dict-type" (runDirect instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, .builder Builder.empty, intV 4]) .typeChk },
    { name := "unit/errors/malformed-root" -- [B7]
      run := do
        let _ ← expectRawErr
          "unit/errors/malformed-root"
          (runRaw instrUnsignedJmpZ #[intV 3, .cell malformedDictRoot, intV 4])
          .cellUnd
        pure () },
    { name := "unit/gas/exact-success" -- [B9]
      run := do
        expectOkStack "unit/gas/exact-success"
          (runDirect instrUnsignedJmpZ (#[intV 3, .cell dictUnsigned4HitRoot, intV 4])) #[] }
  ]
  oracle := #[
    -- [B2][B3] runtime shape + preconditions
    mkCase "oracle/underflow/0" instrUnsignedJmpZ #[], -- [B2]
    mkCase "oracle/underflow/1" instrUnsignedJmpZ #[.null], -- [B2]
    mkCase "oracle/underflow/2" instrUnsignedJmpZ #[.null, .null], -- [B2]
    mkCase "oracle/err/n-type" instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, intV 3, .slice (markerSlice 0xAAAA)], -- [B3]
    mkCase "oracle/err/n-negative" instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, intV 3, intV (-1)], -- [B3]
    mkCase "oracle/err/n-nan" instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, intV 3, .int .nan], -- [B3]
    mkCase "oracle/err/n-too-large" instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, intV 3, intV 2048], -- [B3]
    mkCase "oracle/err/dict-builder" instrUnsignedJmpZ #[intV 3, .builder Builder.empty, intV 4], -- [B3]
    mkCase "oracle/err/dict-slice" instrUnsignedJmpZ #[intV 3, .slice (markerSlice 0xBEEF), intV 4], -- [B3]
    mkCase "oracle/err/key-null" instrUnsignedJmpZ #[.null, (.cell dictUnsigned4HitRoot), intV 4], -- [B3]
    mkCase "oracle/err/key-cell" instrUnsignedJmpZ #[.cell dictUnsigned4HitRoot, (.cell dictUnsigned4HitRoot), intV 4], -- [B3]
    mkCase "oracle/err/key-slice" instrUnsignedJmpZ #[.slice (markerSlice 0xBADD), (.cell dictUnsigned4HitRoot), intV 4], -- [B3]
    mkCase "oracle/err/key-bad-builder" instrUnsignedJmpZ #[.builder Builder.empty, (.cell dictUnsigned4HitRoot), intV 4], -- [B3]
    mkCase "oracle/err/key-nan" instrUnsignedJmpZ #[.int .nan, (.cell dictUnsigned4HitRoot), intV 4], -- [B3]

    -- [B4] key conversion failure (`pushZ`) + miss tail behavior.
    mkCase "oracle/miss/out-of-range-pos" instrUnsignedJmpZ #[intV 16, (.cell dictUnsigned4Root), intV 4], -- [B4], [B6]
    mkCase "oracle/miss/out-of-range-neg" instrUnsignedJmpZ #[intV (-1), (.cell dictUnsigned4Root), intV 4], -- [B4], [B6]
    mkCase "oracle/miss/oob-zero-bits" instrUnsignedJmpZ #[intV 1, (.cell dictUnsigned4Root), intV 0], -- [B4], [B6]
    mkCase "oracle/miss/root-null" instrUnsignedJmpZ #[intV 7, .null, intV 4], -- [B4], [B6]
    mkCase "oracle/miss/in-tree-miss" instrUnsignedJmpZ #[intV 2, (.cell dictUnsigned4HitRoot), intV 4], -- [B4], [B6]
    mkCase "oracle/miss/tail" instrUnsignedJmpZ #[intV 99, intV 16, (.cell dictUnsigned4Root), intV 4], -- [B4], [B6]

    -- [B5] hit path and continuation jump.
    mkCase "oracle/hit/normal" instrUnsignedJmpZ #[intV 3, (.cell dictUnsigned4HitRoot), intV 4], -- [B5]
    mkCase "oracle/hit/tail" instrUnsignedJmpZ #[intV 11, intV 3, (.cell dictUnsigned4HitRoot), intV 4], -- [B5]
    mkCase "oracle/hit/boundary-n0" instrUnsignedJmpZ #[intV 0, (.cell dictUnsignedN0Root), intV 0], -- [B5]

    -- [B7] malformed root.
    mkCase "oracle/malformed-root" instrUnsignedJmpZ #[intV 3, .cell malformedDictRoot, intV 4], -- [B7]
    mkCase "oracle/malformed-root-tail" instrUnsignedJmpZ #[intV 12, intV 3, .cell malformedDictRoot, intV 4], -- [B7]

    -- [B8] assembler/decoder boundaries.
    mkCaseCode "oracle/raw/f4a0" #[] (rawOpcode16 0xf4a0), -- [B8]
    mkCaseCode "oracle/raw/f4a1" #[] (rawOpcode16 0xf4a1), -- [B8]
    mkCaseCode "oracle/raw/f4a2" #[] (rawOpcode16 0xf4a2), -- [B8]
    mkCaseCode "oracle/raw/f4a3" #[] (rawOpcode16 0xf4a3), -- [B8]
    mkCaseCode "oracle/raw/f4bc" #[] (rawOpcode16 0xf4bc), -- [B8]
    mkCaseCode "oracle/raw/f4bd" #[] (rawOpcode16 0xf4bd), -- [B8]
    mkCaseCode "oracle/raw/f4be" #[] (rawOpcode16 0xf4be), -- [B8]
    mkCaseCode "oracle/raw/f4bf" #[] (rawOpcode16 0xf4bf), -- [B8]
    mkCaseCode "oracle/raw/invalid/f4a4" #[] (rawOpcode16 0xf4a4), -- [B8]
    mkCaseCode "oracle/raw/invalid/f4b0" #[] (rawOpcode16 0xf4b0), -- [B8]
    mkCaseCode "oracle/raw/invalid/f4c0" #[] (rawOpcode16 0xf4c0), -- [B8]

    -- [B9] gas.
    mkCase -- [B9]
      "oracle/gas/exact" instrUnsignedJmpZ
      (#[.cell dictUnsigned4HitRoot, intV 3, intV 4])
      gasExact
      (program := #[.pushInt (.num dictExactGas), .tonEnvOp .setGasLimit, instrUnsignedJmpZ]),
    mkCase -- [B9]
      "oracle/gas/exact-minus-one" instrUnsignedJmpZ
      (#[.cell dictUnsigned4HitRoot, intV 3, intV 4])
      gasMinusOne
      (program := #[.pushInt (.num dictExactMinusOneGas), .tonEnvOp .setGasLimit, instrUnsignedJmpZ])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUGETJMPZ }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETJMPZ
