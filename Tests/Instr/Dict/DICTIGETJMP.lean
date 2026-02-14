import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETJMP

/-!
INSTRUCTION: DICTIGETJMP

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch.
2. [B2] Runtime preconditions: `checkUnderflow 3`, `popNatUpTo 1023`, `popMaybeCell`, `popIntFinite` in order.
3. [B3] `n` type/range errors (`.typeChk`, `.rangeChk`).
4. [B4] Dictionary root type errors (`.typeChk` for non-null, non-cell).
5. [B5] Key type/range errors (`.typeChk`, `.intOv`) and key conversion miss via `dictKeyBits?`.
6. [B6] Miss behavior when `pushZ = false` does not push key.
7. [B7] Miss behavior when `pushZ = true` pushes key.
8. [B8] Hit behavior: transfer to ordinary continuation and consume stack.
9. [B9] `doCall = false` => jump transfer path.
10. [B10] `doCall = true` => call transfer path and register new `c0` continuation.
11. [B11] `dictErr` on malformed traversal roots.
12. [B12] Encoding + decoding of opcode families `0xf4a0..0xf4a3` and `0xf4bc..0xf4bf`, and neighbors invalid.
13. [B13] Gas accounting: base cost only, exact-success and exact-minus-one.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn].
Any branch not covered by oracle tests is expected to be hit by the fuzz generator.
-/

private def suiteId : InstrId := { name := "DICTIGETJMP" }

private def instrSignedJmp : Instr := .dictGetExec false false false
private def instrUnsignedJmp : Instr := .dictGetExec true false false
private def instrSignedCall : Instr := .dictGetExec false true false
private def instrUnsignedCall : Instr := .dictGetExec true true false
private def instrSignedJmpZ : Instr := .dictGetExec false false true
private def instrUnsignedJmpZ : Instr := .dictGetExec true false true
private def instrSignedCallZ : Instr := .dictGetExec false true true
private def instrUnsignedCallZ : Instr := .dictGetExec true true true

private def markerSlice (marker : Nat) : Slice := mkSliceFromBits (natToBits marker 16)
private def rawOpcode16 (w16 : Nat) : Cell := Cell.mkOrdinary (natToBits w16 16) #[]

private def jumpTargetSlice : Slice := markerSlice 0xCA11
private def callTargetSlice : Slice := markerSlice 0xC0DE
private def signedHitValue : Slice := markerSlice 0xA111
private def signedMissValue : Slice := markerSlice 0xA222
private def unsignedHitValue : Slice := markerSlice 0xB111
private def unsignedMissValue : Slice := markerSlice 0xB222
private def n0MarkerValue : Slice := markerSlice 0xA000

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
        | none => panic! s!"{label}: unsupported key {k} for n={n} unsigned={unsigned}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some next, _, _, _) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: insertion returned none"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some result => result
    | none => panic! s!"{label}: failed to build dictionary"

private def dictSigned4Hit : Cell :=
  mkDictFromPairs "dictSigned4Hit" 4 false #[(3, jumpTargetSlice)]

private def dictSigned4Call : Cell :=
  mkDictFromPairs "dictSigned4Call" 4 false #[(3, callTargetSlice)]

private def dictSigned4OnlyMiss : Cell :=
  mkDictFromPairs "dictSigned4OnlyMiss" 4 false #[(2, signedMissValue)]

private def dictSigned4Root : Cell :=
  mkDictFromPairs "dictSigned4Root" 4 false #[(3, signedHitValue), (2, signedMissValue)]

private def dictUnsigned4Hit : Cell :=
  mkDictFromPairs "dictUnsigned4Hit" 4 true #[(3, jumpTargetSlice)]

private def dictUnsigned4Call : Cell :=
  mkDictFromPairs "dictUnsigned4Call" 4 true #[(3, callTargetSlice)]

private def dictUnsigned4OnlyMiss : Cell :=
  mkDictFromPairs "dictUnsigned4OnlyMiss" 4 true #[(2, unsignedMissValue)]

private def dictUnsigned4Root : Cell :=
  mkDictFromPairs "dictUnsigned4Root" 4 true #[(3, unsignedHitValue), (2, unsignedMissValue)]

private def dictSignedN0 : Cell :=
  mkDictFromPairs "dictSignedN0" 0 false #[(0, n0MarkerValue)]

private def dictUnsignedN0 : Cell :=
  mkDictFromPairs "dictUnsignedN0" 0 true #[(0, n0MarkerValue)]

private def malformedRootCell : Cell := Cell.mkOrdinary (natToBits 0 2) #[]
private def malformedRoot : Cell := malformedRootCell

private def dispatchSentinel : Int := 77_001
private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
private def sentinelCc : Continuation :=
  .ordinary (Slice.ofCell (Cell.mkOrdinary (natToBits 0xFACE 16) #[])) (.quit 99) OrdCregs.empty OrdCdata.empty
private def sentinelC0 : Continuation := .quit 17
private def regsWithSentinelC0 : Regs := { Regs.initial with c0 := sentinelC0 }

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ =>
      .quit 0

private def dictIGetJmpGasExact : Int := computeExactGasBudget instrSignedJmp
private def dictIGetJmpGasExactMinusOne : Int := computeExactGasBudgetMinusOne instrSignedJmp
private def dictIGetJmpUnsignedGasExact : Int := computeExactGasBudget instrUnsignedJmp
private def dictIGetJmpUnsignedGasExactMinusOne : Int := computeExactGasBudgetMinusOne instrUnsignedJmp

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictIGetJmpGasExact
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictIGetJmpGasExact
private def gasUnsignedExact : OracleGasLimits := oracleGasLimitsExact dictIGetJmpUnsignedGasExact
private def gasUnsignedMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictIGetJmpUnsignedGasExact

private def mkCase (name : String) (instr : Instr) (stack : Array Value)
    (gasLimits : OracleGasLimits := {}) (fuel : Nat := 1_000_000)
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

private def expectJumpTransfer
    (label : String)
    (target : Slice)
    (expectedC0 : Continuation)
    (st : VmState) : IO Unit := do
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code != target then
        throw (IO.userError s!"{label}: expected cc={reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected regs.c0={reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected stack consumed, got {reprStr st.stack}")

private def expectCallTransfer
    (label : String)
    (target : Slice)
    (oldCc : Continuation)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  let expectedC0 := callReturnFromCc oldCc oldC0
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code != target then
        throw (IO.userError s!"{label}: expected cc={reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected regs.c0={reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected stack consumed, got {reprStr st.stack}")

private def expectDecodeStepExact (label : String) (instr : Instr) (w16 : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e => throw (IO.userError s!"{label}: assemble failed {reprStr e}")
  | .ok c =>
      if c.bits != natToBits w16 16 then
        throw (IO.userError s!"{label}: expected bits {natToBits w16 16}, got {c.bits}")
      else
        let _ ← expectDecodeStep label (Slice.ofCell c) instr 16

private def expectDecodeInv (label : String) (w16 : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (rawOpcode16 w16)) with
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode at 0x{Nat.toDigits 16 w16}, got instruction")

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

private def genDICTIGETJMP (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 30
  let rng2 := rng1
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/0" instrSignedJmp #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/1" instrSignedJmp (#[(.null)])
    else if shape = 2 then
      mkCase "fuzz/underflow/2" instrSignedJmp (#[(.cell dictSigned4Root), intV 1])
    else if shape = 3 then
      mkCase "fuzz/err/n-type" instrSignedJmp (#[(.cell dictSigned4Root), intV 3, .slice (markerSlice 0x77AA)])
    else if shape = 4 then
      mkCase "fuzz/err/n-negative" instrSignedJmp (#[(.cell dictSigned4Root), intV 3, intV (-1)])
    else if shape = 5 then
      mkCase "fuzz/err/n-too-large" instrSignedJmp (#[(.cell dictSigned4Root), intV 3, intV 1024])
    else if shape = 6 then
      mkCase "fuzz/err/dict-type" instrSignedJmp (#[(.builder Builder.empty), intV 3, intV 4])
    else if shape = 7 then
      mkCase "fuzz/err/key-type" instrSignedJmp (#[(.cell dictSigned4Root), .slice (markerSlice 0x77AA), intV 4])
    else if shape = 8 then
      mkCase "fuzz/err/key-nan" instrSignedJmp (#[(.cell dictSigned4Root), .int .nan, intV 4])
    else if shape = 9 then
      mkCase "fuzz/signed/miss/oob-pos" instrSignedJmp (#[(.cell dictSigned4Root), intV (-9), intV 4])
    else if shape = 10 then
      mkCase "fuzz/signed/miss/oob-neg" instrSignedJmp (#[(.cell dictSigned4Root), intV 8, intV 4])
    else if shape = 11 then
      mkCase "fuzz/signed/miss/oob-pos-z" instrSignedJmpZ (#[(.cell dictSigned4Root), intV 8, intV 4])
    else if shape = 12 then
      mkCase "fuzz/signed/miss/oob-neg-z" instrSignedJmpZ (#[(.cell dictSigned4Root), intV (-9), intV 4])
    else if shape = 13 then
      mkCase "fuzz/unsigned/miss/oob-pos" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV (-1), intV 4])
    else if shape = 14 then
      mkCase "fuzz/unsigned/miss/oob-neg" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 16, intV 4])
    else if shape = 15 then
      mkCase "fuzz/unsigned/miss/oob-pos-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Root), intV 16, intV 4])
    else if shape = 16 then
      mkCase "fuzz/unsigned/miss/oob-neg-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Root), intV (-1), intV 4])
    else if shape = 17 then
      mkCase "fuzz/signed/hit/jump" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, intV 4])
    else if shape = 18 then
      mkCase "fuzz/signed/hit/call" instrSignedCall (#[(.cell dictSigned4Call), intV 3, intV 4])
    else if shape = 19 then
      mkCase "fuzz/unsigned/hit/jump" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
    else if shape = 20 then
      mkCase "fuzz/unsigned/hit/call" instrUnsignedCall (#[(.cell dictUnsigned4Call), intV 3, intV 4])
    else if shape = 21 then
      mkCase "fuzz/signed/miss/null" instrSignedJmp (#[(.null), intV 3, intV 4])
    else if shape = 22 then
      mkCase "fuzz/unsigned/miss/null-z" instrUnsignedJmpZ (#[(.null), intV 3, intV 4])
    else if shape = 23 then
      mkCase "fuzz/signed/boundary-n0-hit" instrSignedJmp (#[(.cell dictSignedN0), intV 0, intV 0])
    else if shape = 24 then
      mkCase "fuzz/unsigned/boundary-n0-hit" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 0, intV 0])
    else if shape = 25 then
      mkCase "fuzz/malformed/root" instrSignedJmp (#[(.cell malformedRoot), intV 1, intV 4])
    else if shape = 26 then
      mkCase
        "fuzz/gas/exact-signed"
        instrSignedJmp
        (#[(.cell dictSigned4Hit), intV 3, intV 4])
        gasExact
        (program := #[.pushInt (.num dictIGetJmpGasExact), .tonEnvOp .setGasLimit, instrSignedJmp])
    else if shape = 27 then
      mkCase
        "fuzz/gas/exact-minus-one-signed"
        instrSignedJmp
        (#[(.cell dictSigned4Hit), intV 3, intV 4])
        gasExactMinusOne
        (program := #[.pushInt (.num dictIGetJmpGasExactMinusOne), .tonEnvOp .setGasLimit, instrSignedJmp])
    else if shape = 28 then
      mkCase
        "fuzz/gas/exact-unsigned"
        instrUnsignedJmp
        (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
        gasUnsignedExact
        (program := #[.pushInt (.num dictIGetJmpUnsignedGasExact), .tonEnvOp .setGasLimit, instrUnsignedJmp])
    else if shape = 29 then
      mkCase
        "fuzz/gas/exact-minus-one-unsigned"
        instrUnsignedJmp
        (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
        gasUnsignedMinusOne
        (program := #[.pushInt (.num dictIGetJmpUnsignedGasExactMinusOne), .tonEnvOp .setGasLimit, instrUnsignedJmp])
    else
      mkCase
        "fuzz/raw/invalid"
        instrSignedJmp
        (#[(.cell dictSigned4Root), intV 3, intV 4])
        (program := #[.pushInt (.num dictIGetJmpGasExact), .tonEnvOp .setGasLimit, instrSignedJmp])
  let (name', rng3) := addSuffixToCaseName case0.name rng2
  ({ case0 with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let init : Array Value := #[(.cell dictSigned4Hit), intV 3, intV 4]
        let st := runDispatchFallback .add init
        expectOkStack "unit/dispatch/fallback" st #[intV dispatchSentinel] },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let init : Array Value := #[(.cell dictSigned4Hit), intV 3, intV 4]
        let st := runDispatchFallback instrSignedJmp init
        expectOkStack "unit/dispatch/match" st #[] },
    { name := "unit/encode-decode/family" -- [B12]
      run := do
        expectDecodeStepExact "unit/asm/f4a0" instrSignedJmp 0xF4A0
        expectDecodeStepExact "unit/asm/f4a1" instrUnsignedJmp 0xF4A1
        expectDecodeStepExact "unit/asm/f4a2" instrSignedCall 0xF4A2
        expectDecodeStepExact "unit/asm/f4a3" instrUnsignedCall 0xF4A3
        expectDecodeStepExact "unit/asm/f4bc" instrSignedJmpZ 0xF4BC
        expectDecodeStepExact "unit/asm/f4bd" instrUnsignedJmpZ 0xF4BD
        expectDecodeStepExact "unit/asm/f4be" instrSignedCallZ 0xF4BE
        expectDecodeStepExact "unit/asm/f4bf" instrUnsignedCallZ 0xF4BF },
    { name := "unit/decode-invalid-neighbors" -- [B12]
      run := do
        expectDecodeInv "unit/decode/f4a4" 0xF4A4
        expectDecodeInv "unit/decode/f4b0" 0xF4B0
        expectDecodeInv "unit/decode/f4c0" 0xF4C0 },
    { name := "unit/raw/jump-transfer" -- [B9]
      run := do
        let st ←
          expectRawOk
            "unit/raw/jump"
            (runRaw instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, intV 4] ) regsWithSentinelC0 defaultCc)
        expectJumpTransfer
          "unit/raw/jump"
          jumpTargetSlice
          sentinelC0
          st },
    { name := "unit/raw/call-transfer" -- [B10]
      run := do
        let st ←
          expectRawOk
            "unit/raw/call"
            (runRaw
              instrSignedCall
              (#[(.cell dictSigned4Call), intV 3, intV 4])
              regsWithSentinelC0
              sentinelCc)
        expectCallTransfer
          "unit/raw/call"
          callTargetSlice
          sentinelCc
          sentinelC0
          st },
    { name := "unit/raw/malformed-root" -- [B11]
      run := do
        let _ ←
          expectRawErr
            "unit/raw/malformed-root"
            (runRaw instrSignedJmp (#[(.cell malformedRoot), intV 3, intV 4])
            Regs.initial
            defaultCc)
            .dictErr
        pure () }
  ]
  oracle := #[
    -- [B1] basic dispatch covered in unit only.

    -- [B2][B3] Underflow and n checking.
    mkCase "oracle/underflow/0" instrSignedJmp #[],
    mkCase "oracle/underflow/1" instrSignedJmp (#[(.null)]),
    mkCase "oracle/underflow/2" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3]),
    mkCase "oracle/err/n-type" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, .slice (markerSlice 0xCA11)]),
    mkCase "oracle/err/n-negative" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, intV (-1)]),
    mkCase "oracle/err/n-too-large" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, intV 1024]),

    -- [B4] Root type handling.
    mkCase "oracle/err/dict-type-builder" instrSignedJmp (#[(.builder Builder.empty), intV 3, intV 4]),
    mkCase "oracle/err/dict-type-tuple" instrSignedJmp (#[(.tuple #[]), intV 3, intV 4]),
    mkCase "oracle/err/dict-type-null" instrSignedJmp (#[(.null), intV 3, intV 4]),

    -- [B5] Key type/range and conversion miss.
    mkCase "oracle/err/key-type" instrSignedJmp (#[(.cell dictSigned4Hit), .slice (markerSlice 0xCAFE), intV 4]),
    mkCase "oracle/err/key-cell" instrSignedJmp (#[(.cell dictSigned4Hit), .cell Cell.empty, intV 4]),
    mkCase "oracle/err/key-nan" instrSignedJmp (#[(.cell dictSigned4Hit), .int .nan, intV 4]),
    mkCase "oracle/miss-signed-oob-positive-no-z" instrSignedJmp (#[(.cell dictSigned4Hit), intV 8, intV 4]),
    mkCase "oracle/miss-signed-oob-negative-no-z" instrSignedJmp (#[(.cell dictSigned4Hit), intV (-9), intV 4]),
    mkCase "oracle/miss-signed-oob-positive-z" instrSignedJmpZ (#[(.cell dictSigned4Hit), intV 8, intV 4]),
    mkCase "oracle/miss-signed-oob-negative-z" instrSignedJmpZ (#[(.cell dictSigned4Hit), intV (-9), intV 4]),
    mkCase "oracle/miss-unsigned-oob-positive-no-z" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 16, intV 4]),
    mkCase "oracle/miss-unsigned-oob-negative-no-z" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV (-1), intV 4]),
    mkCase "oracle/miss-unsigned-oob-positive-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Hit), intV 16, intV 4]),
    mkCase "oracle/miss-unsigned-oob-negative-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Hit), intV (-1), intV 4]),

    -- [B6][B7] Null/no-hit path and pushZ variants.
    mkCase "oracle/miss-signed-no-root-no-z" instrSignedJmp (#[(.null), intV 3, intV 4]),
    mkCase "oracle/miss-unsigned-no-root-no-z" instrUnsignedJmp (#[(.null), intV 3, intV 4]),
    mkCase "oracle/miss-signed-no-root-z" instrSignedJmpZ (#[(.null), intV 3, intV 4]),
    mkCase "oracle/miss-unsigned-no-root-z" instrUnsignedJmpZ (#[(.null), intV 3, intV 4]),
    mkCase "oracle/miss-signed-in-range" instrSignedJmp (#[(.cell dictSigned4OnlyMiss), intV 2, intV 4]),
    mkCase "oracle/miss-unsigned-in-range" instrUnsignedJmp (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]),
    mkCase "oracle/miss-signed-in-range-z" instrSignedJmpZ (#[(.cell dictSigned4OnlyMiss), intV 2, intV 4]),
    mkCase "oracle/miss-unsigned-in-range-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]),

    -- [B8] Hit path and transfer target coverage.
    mkCase "oracle/hit-signed-jump" instrSignedJmp (#[(.cell dictSigned4Hit), intV 3, intV 4]),
    mkCase "oracle/hit-unsigned-jump" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 3, intV 4]),
    mkCase "oracle/hit-signed-call" instrSignedCall (#[(.cell dictSigned4Call), intV 3, intV 4]),
    mkCase "oracle/hit-unsigned-call" instrUnsignedCall (#[(.cell dictUnsigned4Call), intV 3, intV 4]),

    -- [B10] N=0 boundary entries.
    mkCase "oracle/boundary-signed-n0-hit" instrSignedJmp (#[(.cell dictSignedN0), intV 0, intV 0]),
    mkCase "oracle/boundary-unsigned-n0-hit" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 0, intV 0]),

    -- [B11] Malformed root errors.
    mkCase "oracle/malformed-root-signed" instrSignedJmp (#[(.cell malformedRoot), intV 3, intV 4]),
    mkCase "oracle/malformed-root-unsigned" instrUnsignedJmp (#[(.cell malformedRoot), intV 3, intV 4]),

    -- [B12] Decoder/encoder raw opcode coverage.
    mkCaseCode "oracle/raw/f4a0" (#[(.cell dictSigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A0),
    mkCaseCode "oracle/raw/f4a1" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A1),
    mkCaseCode "oracle/raw/f4a2" (#[(.cell dictSigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A2),
    mkCaseCode "oracle/raw/f4a3" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A3),
    mkCaseCode "oracle/raw/f4bc" (#[(.cell dictSigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BC),
    mkCaseCode "oracle/raw/f4bd" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BD),
    mkCaseCode "oracle/raw/f4be" (#[(.cell dictSigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BE),
    mkCaseCode "oracle/raw/f4bf" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BF),
    mkCaseCode "oracle/raw/invalid-f4a4" #[] (rawOpcode16 0xF4A4),
    mkCaseCode "oracle/raw/invalid-f4c0" #[] (rawOpcode16 0xF4C0),

    -- [B13] Gas behavior.
    mkCase
      "oracle/gas/exact-signed"
      instrSignedJmp
      (#[(.cell dictSigned4Hit), intV 3, intV 4])
      gasExact
      (program := #[.pushInt (.num dictIGetJmpGasExact), .tonEnvOp .setGasLimit, instrSignedJmp]),
    mkCase
      "oracle/gas/exact-minus-one-signed"
      instrSignedJmp
      (#[(.cell dictSigned4Hit), intV 3, intV 4])
      gasExactMinusOne
      (program := #[.pushInt (.num dictIGetJmpGasExactMinusOne), .tonEnvOp .setGasLimit, instrSignedJmp]),
    mkCase
      "oracle/gas/exact-unsigned"
      instrUnsignedJmp
      (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
      gasUnsignedExact
      (program := #[.pushInt (.num dictIGetJmpUnsignedGasExact), .tonEnvOp .setGasLimit, instrUnsignedJmp]),
    mkCase
      "oracle/gas/exact-minus-one-unsigned"
      instrUnsignedJmp
      (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
      gasUnsignedMinusOne
      (program := #[.pushInt (.num dictIGetJmpUnsignedGasExactMinusOne), .tonEnvOp .setGasLimit, instrUnsignedJmp])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTIGETJMP }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETJMP
