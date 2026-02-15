import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETJMP

/-!
INSTRUCTION: DICTUGETJMP

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch.
2. [B2] Runtime preconditions: `checkUnderflow 3`, `popNatUpTo 1023`, `popMaybeCell`, `popIntFinite` in order.
3. [B3] `n` type/range errors (`.typeChk`, `.rangeChk`) in stack precondition checks.
4. [B4] Root type errors (`.typeChk`) for non-`cell`/`null` dictionary root.
5. [B5] Key type/range errors (`.typeChk`, `.intOv`) and conversion miss via `dictKeyBits?`.
6. [B6] Miss behavior when `pushZ = false` leaves stack consumed with no key restoration.
7. [B7] Miss behavior when `pushZ = true` restores original `idx` on stack.
8. [B8] Hit behavior transfers control with `jumpTo` for `doCall = false`.
9. [B9] Hit behavior transfers control with `callTo` for `doCall = true`.
10. [B10] Unsigned key conversion misses:
    - keys negative or `>= 2^n` are misses.
11. [B11] `n = 0` boundary conversion (`idx = 0` only valid).
12. [B12] Assembler/decoder behavior:
    - valid opcode families `0xf4a0..0xf4a3` and `0xf4bc..0xf4bf`
    - invalid neighboring opcodes.
13. [B13] Dictionary traversal errors (`dictErr`) on malformed roots.
14. [B14] Gas accounting: base cost only; exact-success and exact-gas-minus-one tests.

TOTAL BRANCHES: 14

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId := { name := "DICTUGETJMP" }

private def instrSignedJmp : Instr := .dictGetExec false false false
private def instrUnsignedJmp : Instr := .dictGetExec true false false
private def instrSignedCall : Instr := .dictGetExec false true false
private def instrUnsignedCall : Instr := .dictGetExec true true false
private def instrSignedJmpZ : Instr := .dictGetExec false false true
private def instrUnsignedJmpZ : Instr := .dictGetExec true false true
private def instrUnsignedCallZ : Instr := .dictGetExec true true true
private def instrSignedCallZ : Instr := .dictGetExec false true true

private def markerSlice (marker : Nat) : Slice := mkSliceFromBits (natToBits marker 16)
private def rawOpcode16 (w16 : Nat) : Cell := Cell.mkOrdinary (natToBits w16 16) #[]

private def jumpTargetSlice : Slice := markerSlice 0xCA11
private def callTargetSlice : Slice := markerSlice 0xC0DE
private def unsignedHitValue : Slice := markerSlice 0xA111
private def unsignedMissValue : Slice := markerSlice 0xA222
private def n0MarkerValue : Slice := markerSlice 0xF000

private def mkDictFromPairs (label : String) (n : Nat)
    (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let k := pair.1
      let value := pair.2
      let keyBits : BitString :=
        match dictKeyBits? k n true with
        | some bits => bits
        | none => panic! s!"{label}: unsupported key {k} for n={n}"
      match dictSetSliceWithCells root keyBits value .set with
      | .ok (some next, _, _, _) => root := some next
      | .ok (none, _, _, _) => panic! s!"{label}: insertion returned none"
      | .error e => panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some result => result
    | none => panic! s!"{label}: failed to build dictionary"

private def dictUnsigned4Hit : Cell :=
  mkDictFromPairs "dictUnsigned4Hit" 4 #[(3, unsignedHitValue)]

private def dictUnsigned4Call : Cell :=
  mkDictFromPairs "dictUnsigned4Call" 4 #[(3, callTargetSlice)]

private def dictUnsigned4OnlyMiss : Cell :=
  mkDictFromPairs "dictUnsigned4OnlyMiss" 4 #[(2, unsignedMissValue)]

private def dictUnsigned4Root : Cell :=
  mkDictFromPairs "dictUnsigned4Root" 4 #[(3, unsignedHitValue), (2, unsignedMissValue)]

private def dictUnsignedN0 : Cell :=
  mkDictFromPairs "dictUnsignedN0" 0 #[(0, n0MarkerValue)]

private def malformedRootCell : Cell := Cell.mkOrdinary (natToBits 0 2) #[]
private def malformedRoot : Cell := malformedRootCell

private def dispatchSentinel : Int := 77_001
private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
private def sentinelCc : Continuation := .ordinary (Slice.ofCell (Cell.mkOrdinary (natToBits 0xFACE 16) #[])) (.quit 99) OrdCregs.empty OrdCdata.empty
private def sentinelC0 : Continuation := .quit 17
private def regsWithSentinelC0 : Regs := { Regs.initial with c0 := sentinelC0 }

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ => .quit 0

private def dictUGetJmpGasExact : Int := computeExactGasBudget instrUnsignedJmp
private def dictUGetJmpGasExactMinusOne : Int := computeExactGasBudgetMinusOne instrUnsignedJmp

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictUGetJmpGasExact
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictUGetJmpGasExact

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
      if code.toCellRemaining != target.toCellRemaining then
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
      if code.toCellRemaining != target.toCellRemaining then
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
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode, got instruction")

private def addSuffixToCaseName (name : String) (rng0 : StdGen) : String × StdGen :=
  let (sfx, rng1) := randNat rng0 0 999_999
  (s!"{name}/{sfx}", rng1)

private def genDICTUGETJMP (rng0 : StdGen) : OracleCase × StdGen :=
  let (bucket, rng1) := randNat rng0 0 99
  let (shape, rng2) :=
    if bucket < 70 then
      randNat rng1 0 23
    else
      randNat rng1 0 11
  let case0 : OracleCase :=
    if bucket < 70 then
      if shape = 0 then
        mkCase "fuzz/underflow/0" instrUnsignedJmp #[] -- [B1][B2]
      else if shape = 1 then
        mkCase "fuzz/underflow/1" instrUnsignedJmp #[(.null)] -- [B1][B2]
      else if shape = 2 then
        mkCase "fuzz/underflow/2" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 1]) -- [B1][B2]
      else if shape = 3 then
        mkCase "fuzz/err/n-type" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, .slice (markerSlice 0x77AA)]) -- [B3]
      else if shape = 4 then
        mkCase "fuzz/err/n-negative" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, intV (-1)]) -- [B3]
      else if shape = 5 then
        mkCase "fuzz/err/n-too-large" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, intV 1024]) -- [B3]
      else if shape = 6 then
        mkCase "fuzz/err/dict-type" instrUnsignedJmp (#[(.builder Builder.empty), intV 3, intV 4]) -- [B4]
      else if shape = 7 then
        mkCase "fuzz/err/root-malformed" instrUnsignedJmp (#[(.cell malformedRoot), intV 3, intV 4]) -- [B13]
      else if shape = 8 then
        mkCase "fuzz/err/key-type" instrUnsignedJmp (#[(.cell dictUnsigned4Root), .slice (markerSlice 0x77AA), intV 4]) -- [B5]
      else if shape = 9 then
        mkCase "fuzz/err/key-nan" instrUnsignedJmp (#[(.cell dictUnsigned4Root), .int .nan, intV 4]) -- [B5]
      else if shape = 10 then
        mkCase "fuzz/miss/oob-positive" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 16, intV 4]) -- [B10][B6]
      else if shape = 11 then
        mkCase "fuzz/miss/oob-negative" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV (-1), intV 4]) -- [B10][B6]
      else if shape = 12 then
        mkCase "fuzz/miss/oob-positive-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Root), intV 16, intV 4]) -- [B10][B7]
      else if shape = 13 then
        mkCase "fuzz/miss/oob-negative-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Root), intV (-1), intV 4]) -- [B10][B7]
      else if shape = 14 then
        mkCase "fuzz/miss/no-root-no-z" instrUnsignedJmp (#[(.null), intV 3, intV 4]) -- [B6]
      else if shape = 15 then
        mkCase "fuzz/miss/no-root-z" instrUnsignedJmpZ (#[(.null), intV 3, intV 4]) -- [B7]
      else if shape = 16 then
        mkCase "fuzz/hit/jump" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) -- [B8]
      else if shape = 17 then
        mkCase "fuzz/hit/call" instrUnsignedCall (#[(.cell dictUnsigned4Call), intV 3, intV 4]) -- [B9]
      else if shape = 18 then
        mkCase "fuzz/hit/call-z" instrUnsignedCallZ (#[(.cell dictUnsigned4Call), intV 3, intV 4]) -- [B9][B7]
      else if shape = 19 then
        mkCase "fuzz/miss/in-range" instrUnsignedJmp (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]) -- [B6]
      else if shape = 20 then
        mkCase "fuzz/n0-miss" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 1, intV 0]) -- [B10][B11]
      else if shape = 21 then
        mkCase
          "fuzz/gas/exact"
          instrUnsignedJmp
          (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
          gasExact
          (program := #[.pushInt (.num dictUGetJmpGasExact), .tonEnvOp .setGasLimit, instrUnsignedJmp]) -- [B14]
      else if shape = 22 then
        mkCase
          "fuzz/gas/exact-minus-one"
          instrUnsignedJmp
          (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
          gasExactMinusOne
          (program := #[.pushInt (.num dictUGetJmpGasExactMinusOne), .tonEnvOp .setGasLimit, instrUnsignedJmp]) -- [B14]
      else if shape = 23 then
        mkCase "fuzz/miss/in-range-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]) -- [B7]
      else
        mkCase "fuzz/root/type-mismatch" instrUnsignedJmp (#[(.tuple #[]), intV 4, intV 4]) -- [B4]
    else
      if shape = 0 then
        mkCase "fuzz/random/hit" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) -- [B8]
      else if shape = 1 then
        mkCase "fuzz/random/call" instrUnsignedCall (#[(.cell dictUnsigned4Call), intV 3, intV 4]) -- [B9]
      else if shape = 2 then
        mkCase "fuzz/random/no-root" instrUnsignedJmp (#[(.null), intV 3, intV 4]) -- [B6]
      else if shape = 3 then
        mkCase "fuzz/random/key-min" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 0, intV 4]) -- [B10]
      else if shape = 4 then
        mkCase "fuzz/random/key-max" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 15, intV 4]) -- [B8]
      else if shape = 5 then
        mkCase "fuzz/random/hit-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) -- [B7][B8]
      else if shape = 6 then
        mkCase "fuzz/random/out-of-range-neg" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV (-3), intV 4]) -- [B10]
      else if shape = 7 then
        mkCase "fuzz/random/out-of-range-pos" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 16, intV 4]) -- [B10]
      else if shape = 8 then
        mkCase "fuzz/random/n0-hit" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 0, intV 0]) -- [B11]
      else if shape = 9 then
        mkCase "fuzz/random/root-malformed" instrUnsignedJmp (#[(.cell malformedRoot), intV 3, intV 4]) -- [B13]
      else if shape = 10 then
        mkCase
          "fuzz/random/gas-exact"
          instrUnsignedJmp
          (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
          gasExact
          (program := #[.pushInt (.num dictUGetJmpGasExact), .tonEnvOp .setGasLimit, instrUnsignedJmp]) -- [B14]
      else
        mkCase "fuzz/random/key-absent" instrUnsignedJmp (#[(.cell dictUnsigned4OnlyMiss), intV 7, intV 4]) -- [B6]
  let (name', rng3) := addSuffixToCaseName case0.name rng2
  ({ case0 with name := name' }, rng3)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let init : Array Value := #[intV 3, (.cell dictUnsigned4Hit), intV 4]
        let st := runDispatchFallback .add init
        expectOkStack "unit/dispatch/fallback" st (init ++ #[intV dispatchSentinel]) },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let init : Array Value := #[intV 3, (.cell dictUnsigned4Hit), intV 4]
        let st := runDispatchFallback instrUnsignedJmp init
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
    { name := "unit/raw/jump-transfer" -- [B8]
      run := do
        let st ←
          expectRawOk
            "unit/raw/jump"
            (runRaw instrUnsignedJmp (#[intV 3, (.cell dictUnsigned4Hit), intV 4]) regsWithSentinelC0 defaultCc)
        expectJumpTransfer
          "unit/raw/jump"
          unsignedHitValue
          sentinelC0
          st },
    { name := "unit/raw/call-transfer" -- [B9]
      run := do
        let st ←
          expectRawOk
            "unit/raw/call"
            (runRaw
              instrUnsignedCall
              (#[intV 3, (.cell dictUnsigned4Call), intV 4])
              regsWithSentinelC0
              sentinelCc)
        expectCallTransfer
          "unit/raw/call"
          callTargetSlice
          sentinelCc
          sentinelC0
          st },
    { name := "unit/raw/malformed-root" -- [B13]
      run := do
        let _ ←
          expectRawErr
            "unit/raw/malformed-root"
            (runRaw instrUnsignedJmp (#[intV 3, (.cell malformedRoot), intV 4])
            Regs.initial
            defaultCc)
            .dictErr
        pure () }
  ]
  oracle := #[
    mkCase "oracle/underflow/0" instrUnsignedJmp #[], -- [B1][B2]
    mkCase "oracle/underflow/1" instrUnsignedJmp #[(.null)], -- [B1][B2]
    mkCase "oracle/underflow/2" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3]), -- [B1][B2]
    mkCase "oracle/err/n-type" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, .slice (markerSlice 0xCA11)]), -- [B3]
    mkCase "oracle/err/n-negative" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, intV (-1)]), -- [B3]
    mkCase "oracle/err/n-too-large" instrUnsignedJmp (#[(.cell dictUnsigned4Root), intV 3, intV 1024]), -- [B3]
    mkCase "oracle/err/dict-type-builder" instrUnsignedJmp (#[(.builder Builder.empty), intV 3, intV 4]), -- [B4]
    mkCase "oracle/err/dict-type-tuple" instrUnsignedJmp (#[(.tuple #[]), intV 3, intV 4]), -- [B4]
    mkCase "oracle/err/dict-type-null" instrUnsignedJmp (#[(.null), intV 3, intV 4]), -- [B4]
    mkCase "oracle/err/key-type" instrUnsignedJmp (#[(.cell dictUnsigned4Root), .slice (markerSlice 0xCAFE), intV 4]), -- [B5]
    mkCase "oracle/err/key-cell" instrUnsignedJmp (#[(.cell dictUnsigned4Root), .cell Cell.empty, intV 4]), -- [B5]
    mkCase "oracle/err/key-nan" instrUnsignedJmp (#[(.cell dictUnsigned4Root), .int .nan, intV 4]), -- [B5]
    mkCase "oracle/miss-unsigned-oob-positive-no-z" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 16, intV 4]), -- [B10][B6]
    mkCase "oracle/miss-unsigned-oob-negative-no-z" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV (-1), intV 4]), -- [B10][B6]
    mkCase "oracle/miss-unsigned-oob-positive-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Hit), intV 16, intV 4]), -- [B10][B7]
    mkCase "oracle/miss-unsigned-oob-negative-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4Hit), intV (-1), intV 4]), -- [B10][B7]
    mkCase "oracle/miss-no-root-no-z" instrUnsignedJmp (#[(.null), intV 3, intV 4]), -- [B6]
    mkCase "oracle/miss-no-root-z" instrUnsignedJmpZ (#[(.null), intV 3, intV 4]), -- [B7]
    mkCase "oracle/miss-in-range-no-z" instrUnsignedJmp (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]), -- [B6]
    mkCase "oracle/miss-in-range-z" instrUnsignedJmpZ (#[(.cell dictUnsigned4OnlyMiss), intV 2, intV 4]), -- [B7]
    mkCase "oracle/hit-unsigned-jump" instrUnsignedJmp (#[(.cell dictUnsigned4Hit), intV 3, intV 4]), -- [B8]
    mkCase "oracle/hit-unsigned-call" instrUnsignedCall (#[(.cell dictUnsigned4Call), intV 3, intV 4]), -- [B9]
    mkCase "oracle/hit-unsigned-call-z" instrUnsignedCallZ (#[(.cell dictUnsigned4Call), intV 3, intV 4]), -- [B9][B7]
    mkCase "oracle/boundary-unsigned-n0-hit" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 0, intV 0]), -- [B11]
    mkCase "oracle/boundary-n0-miss" instrUnsignedJmp (#[(.cell dictUnsignedN0), intV 1, intV 0]), -- [B10][B11]
    mkCase "oracle/malformed-root-unsigned" instrUnsignedJmp (#[(.cell malformedRoot), intV 3, intV 4]), -- [B13]
    mkCaseCode "oracle/raw/f4a0" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A0), -- [B12]
    mkCaseCode "oracle/raw/f4a1" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A1), -- [B12]
    mkCaseCode "oracle/raw/f4a2" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A2), -- [B12]
    mkCaseCode "oracle/raw/f4a3" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4A3), -- [B12]
    mkCaseCode "oracle/raw/f4bc" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BC), -- [B12]
    mkCaseCode "oracle/raw/f4bd" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BD), -- [B12]
    mkCaseCode "oracle/raw/f4be" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BE), -- [B12]
    mkCaseCode "oracle/raw/f4bf" (#[(.cell dictUnsigned4Hit), intV 3, intV 4]) (rawOpcode16 0xF4BF), -- [B12]
    mkCaseCode "oracle/raw/invalid-f4a4" #[] (rawOpcode16 0xF4A4), -- [B12]
    mkCaseCode "oracle/raw/invalid-f4b0" #[] (rawOpcode16 0xF4B0), -- [B12]
    mkCaseCode "oracle/raw/invalid-f4c0" #[] (rawOpcode16 0xF4C0), -- [B12]
    mkCase
      "oracle/gas/exact" -- [B14]
      instrUnsignedJmp
      (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
      gasExact
      (program := #[.pushInt (.num dictUGetJmpGasExact), .tonEnvOp .setGasLimit, instrUnsignedJmp]),
    mkCase
      "oracle/gas/exact-minus-one" -- [B14]
      instrUnsignedJmp
      (#[(.cell dictUnsigned4Hit), intV 3, intV 4])
      gasExactMinusOne
      (program := #[.pushInt (.num dictUGetJmpGasExactMinusOne), .tonEnvOp .setGasLimit, instrUnsignedJmp])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTUGETJMP }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETJMP
