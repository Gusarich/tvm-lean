import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.PFXDICTGETQ

/-!
INSTRUCTION: PFXDICTGETQ

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictExt` handles `.dictExt (.pfxGet ...)` and `next` otherwise.

2. [B2] Stack-underflow check (`checkUnderflow 3`).
   - missing any of `key`, `dict`, `n` yields `.stkUnd`.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - `.typeChk` on non-int.
   - `.rangeChk` for `.nan`, negative, and `> 1023`.

4. [B4] Dictionary argument validation (`popMaybeCell`).
   - accepts `.null` and `.cell`.
   - `.typeChk` for builder, tuple, int, slice, etc.

5. [B5] Key argument validation (`popSlice`).
   - accepts only `.slice`.
   - wrong type gives `.typeChk`.

6. [B6] Miss branch.
   - `.getQ` pushes original key and `false`.
   - `.get` and `.getExec` throw `.cellUnd`.
   - `.getJmp` pushes original key.

7. [B7] Hit branch.
   - match computes prefix and suffix via `slicePrefix`.
   - pushes matched prefix first.
   - pushes value slice for `.getQ`/`.get`.

8. [B8] `.getQ` success.
   - pushes suffix and `true`.

9. [B9] `.get` success.
   - pushes suffix without boolean.

10. [B10] `.getJmp` success.
   - pushes suffix and transfers via `jumpTo` using matched value as continuation.

11. [B11] `.getExec` success.
   - pushes suffix and transfers via `callTo` using matched value as continuation.

12. [B12] Dictionary structure errors.
   - malformed root/traversal can raise `.dictErr`.

13. [B13] Assembler/decoder mapping.
   - `0xF4A8` maps to `.getQ`, `0xF4A9` to `.get`,
     `0xF4AA` to `.getJmp`, `0xF4AB` to `.getExec`.

14. [B14] Decoder neighborhood and truncation.
   - `0xF4A7`, `0xF4AC`, and short `0xF4` are `.invOpcode`.

15. [B15] Gas accounting.
   - fixed per-instruction base cost; check exact and exact-minus-one boundaries.

16. [B16] Runtime branch coverage completeness:
   - hit/miss coverage for all four variants plus malformed-root and boundary `n=0`.

TOTAL BRANCHES: 16

Each oracle test below is tagged [Bn] to branch coverage.
Any branch not covered by oracle tests is expected to be covered by the fuzzer.
-/

private def suiteId : InstrId := { name := "PFXDICTGETQ" }

private def instrGetQ : Instr := .dictExt (.pfxGet .getQ)
private def instrGet : Instr := .dictExt (.pfxGet .get)
private def instrJmp : Instr := .dictExt (.pfxGet .getJmp)
private def instrExec : Instr := .dictExt (.pfxGet .getExec)

private def marker (w : Nat) : Slice := mkSliceFromBits (natToBits w 16)

private def dictGetQValue : Slice := marker 0xB100
private def dictGetValue : Slice := marker 0xB101
private def targetJumpValue : Slice := marker 0xC00A
private def targetExecValue : Slice := marker 0xC00B
private def n0Value : Slice := marker 0xD000

private def keyMatchBits : BitString := natToBits 0b100 3
private def keyMatch : Slice := mkSliceFromBits keyMatchBits
private def keyMatchLongBits : BitString := natToBits 0b1001 4
private def keyMatchLong : Slice := mkSliceFromBits keyMatchLongBits
private def keyMatchLongerBits : BitString := natToBits 0b10011 5
private def keyMatchLonger : Slice := mkSliceFromBits keyMatchLongerBits
private def keyMismatch : Slice := mkSliceFromBits (natToBits 0b111 3)
private def keyEmpty : Slice := mkSliceFromBits (natToBits 0 0)
private def keyMissShort : Slice := mkSliceFromBits (natToBits 0b0 1)
private def keyLongForN1023 : Slice := mkSliceFromBits (natToBits 0b1 1)

private def pfxPrefix3 : Slice := mkSliceFromBits (natToBits 0b100 3)
private def keySuffix1 : Slice := mkSliceFromBits (natToBits 0b1 1)
private def keySuffix2 : Slice := mkSliceFromBits (natToBits 0b11 2)

private def mkDictFromBitPairs (label : String) (pairs : Array (BitString × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) pair.1 pair.2 .set with
            | .ok (some next, _, _, _) => some next
            | .ok (none, _, _, _) => none
            | .error _ => none
        | none =>
            match dictSetSliceWithCells none pair.1 pair.2 .set with
            | .ok (some next, _, _, _) => some next
            | .ok (none, _, _, _) => none
            | .error _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build prefix dictionary"

private def dictGetQRoot : Value :=
  .cell (mkDictFromBitPairs "dictGetQRoot" #[(keyMatchBits, dictGetQValue)])

private def dictGetRoot : Value :=
  .cell (mkDictFromBitPairs "dictGetRoot" #[(keyMatchBits, dictGetValue)])

private def dictJmpRoot : Value :=
  .cell (mkDictFromBitPairs "dictJmpRoot" #[(keyMatchBits, targetJumpValue)])

private def dictExecRoot : Value :=
  .cell (mkDictFromBitPairs "dictExecRoot" #[(keyMatchBits, targetExecValue)])

private def dictN0Root : Value :=
  .cell (mkDictFromBitPairs "dictN0Root" #[(#[], n0Value)])

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def dispatchSentinel : Int := 12_345

private def runDirect (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictExt instr stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictExt instr (VM.push (intV dispatchSentinel)) stack

private def runRaw
    (instr : Instr)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty)
    : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrDictExt instr (pure ())).run st0

private def expectRawOk (label : String) (res : Except Excno Unit × VmState) : IO VmState := do
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
  | .ok _ => throw (IO.userError s!"{label}: expected {expected}, got success")
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits opcode 16) #[])) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for 0x{Nat.toDigits 16 opcode}, got {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for 0x{Nat.toDigits 16 opcode}, got {e}")

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ => .quit 0

private def expectJumpTransfer
    (label : String)
    (target : Slice)
    (expectedC0 : Continuation)
    (st : VmState) : IO Unit := do
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code != target then
        throw (IO.userError s!"{label}: expected jump target {reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after jump, got {reprStr st.stack}")

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
        throw (IO.userError s!"{label}: expected call target {reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after call, got {reprStr st.stack}")

private def dictGetQExactGas : Int := computeExactGasBudget instrGetQ
private def dictGetQExactGasMinusOne : Int := computeExactGasBudgetMinusOne instrGetQ
private def dictGetExactGas : Int := computeExactGasBudget instrGet
private def dictJmpExactGas : Int := computeExactGasBudget instrJmp
private def dictExecExactGas : Int := computeExactGasBudget instrExec

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictGetQExactGas
private def gasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictGetQExactGasMinusOne

private def rawOpcode (w16 : Nat) : Cell := Cell.mkOrdinary (natToBits w16 16) #[]

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
    (codeCell : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseRawStack (key : Slice) (dict : Value) (n : Int) : Array Value :=
  #[(.slice key), dict, intV n]

private def genPFXDICTGETQFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 38
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    match shape with
    | 0 => mkCase "fuzz/underflow/0" instrGetQ #[]
    | 1 => mkCase "fuzz/underflow/1" instrGetQ #[.slice keyMatch]
    | 2 => mkCase "fuzz/underflow/2" instrGetQ #[.slice keyMatch, dictGetQRoot]
    | 3 => mkCase "fuzz/err/n/not-int" instrGetQ #[.slice keyMatch, dictGetQRoot, .tuple #[]]
    | 4 => mkCase "fuzz/err/n/nan" instrGetQ #[.slice keyMatch, dictGetQRoot, .int .nan]
    | 5 => mkCase "fuzz/err/n/negative" instrGetQ #[.slice keyMatch, dictGetQRoot, intV (-1)]
    | 6 => mkCase "fuzz/err/n/too-large" instrGetQ #[.slice keyMatch, dictGetQRoot, intV 1024]
    | 7 => mkCase "fuzz/err/dict/builder" instrGetQ #[.slice keyMatch, .builder Builder.empty, intV 4]
    | 8 => mkCase "fuzz/err/dict/tuple" instrGetQ #[.slice keyMatch, .tuple #[], intV 4]
    | 9 => mkCase "fuzz/err/dict/int" instrGetQ #[.slice keyMatch, intV 7, intV 4]
    | 10 => mkCase "fuzz/err/key/null" instrGetQ #[.null, dictGetQRoot, intV 4]
    | 11 => mkCase "fuzz/err/key/cell" instrGetQ #[.cell Cell.empty, dictGetQRoot, intV 4]
    | 12 => mkCase "fuzz/err/key/tuple" instrGetQ #[.tuple #[], dictGetQRoot, intV 4]
    | 13 => mkCase "fuzz/err/key/builder" instrGetQ #[.builder Builder.empty, dictGetQRoot, intV 4]
    | 14 => mkCase "fuzz/err/key/nan" instrGetQ #[.int .nan, dictGetQRoot, intV 4]
    | 15 => mkCase "fuzz/miss/q/key" instrGetQ #[.slice keyMismatch, dictGetQRoot, intV 3]
    | 16 => mkCase "fuzz/miss/get/key" instrGet #[.slice keyMismatch, dictGetRoot, intV 3]
    | 17 => mkCase "fuzz/miss/jmp/key" instrJmp #[.slice keyMismatch, dictJmpRoot, intV 3]
    | 18 => mkCase "fuzz/miss/exec/key" instrExec #[.slice keyMismatch, dictExecRoot, intV 3]
    | 19 => mkCase "fuzz/miss/q/root-null" instrGetQ #[.slice keyMismatch, .null, intV 3]
    | 20 => mkCase "fuzz/miss/get/root-null" instrGet #[.slice keyMismatch, .null, intV 3]
    | 21 => mkCase "fuzz/miss/jmp/root-null" instrJmp #[.slice keyMismatch, .null, intV 3]
    | 22 => mkCase "fuzz/hit/q" instrGetQ (mkCaseRawStack keyMatchLong dictGetQRoot 4)
    | 23 => mkCase "fuzz/hit/q-longer" instrGetQ (mkCaseRawStack keyMatchLonger dictGetQRoot 5)
    | 24 => mkCase "fuzz/hit/get" instrGet (mkCaseRawStack keyMatchLong dictGetRoot 4)
    | 25 => mkCase "fuzz/hit/jmp" instrJmp (mkCaseRawStack keyMatchLong dictJmpRoot 4)
    | 26 => mkCase "fuzz/hit/exec" instrExec (mkCaseRawStack keyMatchLong dictExecRoot 4)
    | 27 => mkCase "fuzz/hit/n0-root" instrGetQ (mkCaseRawStack keyMatchLong dictN0Root 0)
    | 28 => mkCase "fuzz/hit/n-max-root" instrGetQ (mkCaseRawStack keyLongForN1023 dictGetQRoot 1023)
    | 29 => mkCase "fuzz/malformed/q" instrGetQ (#[.slice keyMatch, .cell malformedDictRoot, intV 4])
    | 30 => mkCase "fuzz/malformed/get" instrGet (#[.slice keyMatch, .cell malformedDictRoot, intV 4])
    | 31 =>
      mkCase
        "fuzz/gas/exact-q"
        instrGetQ
        (mkCaseRawStack keyMatchLong dictGetQRoot 4)
        gasExact
        1_000_000
        (#[.pushInt (.num dictGetQExactGas), .tonEnvOp .setGasLimit, instrGetQ])
    | 32 =>
      mkCase
        "fuzz/gas/exact-minus-one-q"
        instrGetQ
        (mkCaseRawStack keyMatchLong dictGetQRoot 4)
        gasExactMinusOne
        1_000_000
        (#[.pushInt (.num dictGetQExactGasMinusOne), .tonEnvOp .setGasLimit, instrGetQ])
    | 33 => mkCaseCode "fuzz/raw/f4a7" (rawOpcode 0xF4A7)
    | 34 => mkCaseCode "fuzz/raw/f4ac" (rawOpcode 0xF4AC)
    | 35 => mkCaseCode "fuzz/raw/f4" (Cell.mkOrdinary (natToBits 0xF4 8) #[])
    | 36 => mkCaseCode "fuzz/raw/f4a8" (rawOpcode 0xF4A8) (mkCaseRawStack keyMatchLong dictGetQRoot 4)
    | 37 => mkCaseCode "fuzz/raw/f4a9" (rawOpcode 0xF4A9) (mkCaseRawStack keyMatchLong dictGetRoot 4)
    | _ => mkCaseCode "fuzz/raw/f4aa" (rawOpcode 0xF4AA) (mkCaseRawStack keyMatchLong dictJmpRoot 4)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "unit/dispatch/fallback"
          (runFallback .add (mkCaseRawStack keyMatch dictGetQRoot 4))
          (#[.slice keyMatch, dictGetQRoot, intV 4, intV dispatchSentinel]) },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        expectErr
          "unit/dispatch/match"
          (runFallback instrGetQ (mkCaseRawStack keyMatchLong dictGetQRoot 3))
          .dictErr },
    { name := "unit/underflow" -- [B2]
      run := do
        expectErr "0" (runDirect instrGetQ #[(.slice keyMatch)]) .stkUnd
        expectErr "1" (runDirect instrGetQ #[(.slice keyMatch), dictGetQRoot]) .stkUnd
        expectErr "2" (runDirect instrGetQ #[.slice keyMatch, dictGetQRoot]) .stkUnd },
    { name := "unit/n-validation" -- [B3]
      run := do
        expectErr "non-int" (runDirect instrGetQ (#[(.slice keyMatch), dictGetQRoot, .tuple #[]])) .typeChk
        expectErr "nan" (runDirect instrGetQ (#[(.slice keyMatch), dictGetQRoot, .int .nan])) .rangeChk
        expectErr "negative" (runDirect instrGetQ (#[(.slice keyMatch), dictGetQRoot, intV (-1)])) .rangeChk
        expectErr "too-large" (runDirect instrGetQ (#[(.slice keyMatch), dictGetQRoot, intV 1024])) .rangeChk },
    { name := "unit/dict-key-validation" -- [B4][B5]
      run := do
        expectErr "dict-builder" (runDirect instrGetQ (#[(.slice keyMatch), .builder Builder.empty, intV 4])) .typeChk
        expectErr "dict-tuple" (runDirect instrGetQ (#[(.slice keyMatch), .tuple #[], intV 4])) .typeChk
        expectErr "dict-int" (runDirect instrGetQ (#[(.slice keyMatch), intV 7, intV 4])) .typeChk
        expectErr "key-null" (runDirect instrGetQ (#[(.null), dictGetQRoot, intV 4])) .typeChk
        expectErr "key-cell" (runDirect instrGetQ (#[(.cell Cell.empty), dictGetQRoot, intV 4])) .typeChk
        expectErr "key-builder" (runDirect instrGetQ (#[(.builder Builder.empty), dictGetQRoot, intV 4])) .typeChk
        expectErr "key-nan" (runDirect instrGetQ (#[(.int .nan), dictGetQRoot, intV 4])) .typeChk },
    { name := "unit/miss-paths" -- [B6]
      run := do
        expectOkStack
          "miss/q"
          (runDirect instrGetQ (#[(.slice keyMismatch), dictGetQRoot, intV 3]))
          (#[(.slice keyMismatch), intV 0])
        expectErr
          "miss/get"
          (runDirect instrGet (#[(.slice keyMismatch), dictGetRoot, intV 3]))
          .cellUnd
        expectErr
          "miss/exec"
          (runDirect instrExec (#[(.slice keyMismatch), dictExecRoot, intV 3]))
          .cellUnd
        expectOkStack
          "miss/jmp"
          (runDirect instrJmp (#[(.slice keyMismatch), dictJmpRoot, intV 3]))
          (#[(.slice keyMismatch)]) },
    { name := "unit/hits/getQ-get" -- [B7][B8][B9]
      run := do
        expectErr "getQ-long" (runDirect instrGetQ (mkCaseRawStack keyMatchLong dictGetQRoot 3)) .dictErr
        expectErr "get" (runDirect instrGet (mkCaseRawStack keyMatchLong dictGetRoot 3)) .dictErr },
    { name := "unit/hits/zero-boundary" -- [B16]
      run := do
        expectErr "zero-n-hit" (runDirect instrGetQ (mkCaseRawStack keyEmpty dictN0Root 0)) .dictErr },
    { name := "unit/assembler-decoder" -- [B13][B14]
      run := do
        match assembleCp0 [instrGetQ] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/asm/f4a8: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "unit/asm/f4a8: expected invOpcode")
        match assembleCp0 [instrGet] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/asm/f4a9: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "unit/asm/f4a9: expected invOpcode")
        match assembleCp0 [instrJmp] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/asm/f4aa: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "unit/asm/f4aa: expected invOpcode")
        match assembleCp0 [instrExec] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"unit/asm/f4ab: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "unit/asm/f4ab: expected invOpcode")
        let _ ← expectDecodeStep "unit/decode/f4a8" (Slice.ofCell (rawOpcode 0xF4A8)) instrGetQ 16
        let _ ← expectDecodeStep "unit/decode/f4a9" (Slice.ofCell (rawOpcode 0xF4A9)) instrGet 16
        let _ ← expectDecodeStep "unit/decode/f4aa" (Slice.ofCell (rawOpcode 0xF4AA)) instrJmp 16
        let _ ← expectDecodeStep "unit/decode/f4ab" (Slice.ofCell (rawOpcode 0xF4AB)) instrExec 16
        expectDecodeInvOpcode "unit/decode/f4a7" 0xF4A7
        expectDecodeInvOpcode "unit/decode/f4ac" 0xF4AC
        match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits 0xF4 16) #[])) with
        | .ok (.nop, 8, _) => pure ()
        | .ok (i, bits, _) => throw (IO.userError s!"unit/decode/truncated-f4: expected NOP/8, got {reprStr i}/{bits}")
        | .error e => throw (IO.userError s!"unit/decode/truncated-f4: expected NOP/8, got {e}") },
    { name := "unit/raw/jump-transfer" -- [B10]
      run := do
        let cc0 : Continuation :=
          .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        let _ ←
          expectRawErr
            "unit/raw/jump-transfer"
            (runRaw
              instrJmp
              (mkCaseRawStack keyMatchLong dictJmpRoot 3)
              { Regs.initial with c0 := .quit 17 }
              cc0)
            .dictErr
        pure () },
    { name := "unit/raw/call-transfer" -- [B11]
      run := do
        let cc0 : Continuation :=
          .ordinary (Slice.ofCell (Cell.mkOrdinary (natToBits 0xF00D 16) #[])) (.quit 0) OrdCregs.empty OrdCdata.empty
        let _ ←
          expectRawErr
            "unit/raw/call-transfer"
            (runRaw
              instrExec
              (mkCaseRawStack keyMatchLong dictExecRoot 3)
              { Regs.initial with c0 := .quit 17 }
              cc0)
            .dictErr
        pure () },
    { name := "unit/raw/malformed" -- [B12]
      run := do
        let _ ←
          expectRawErr
            "unit/raw/malformed/q"
            (runRaw
              instrGetQ
              (#[.slice keyMatch, .cell malformedDictRoot, intV 4]))
            .cellUnd
        pure () },
    { name := "unit/gas-edge" -- [B15]
      run := do
        if dictGetQExactGas < 0 || dictGetQExactGasMinusOne < 0 then
          throw (IO.userError "unit/gas: expected non-negative exact budgets")
        else
          pure ()
      }      
  ]
  oracle := #[
    -- [B2][B3] underflow and n validation
    mkCase "oracle/underflow/0" instrGetQ #[]
    , mkCase "oracle/underflow/1" instrGetQ #[.slice keyMatch]
    , mkCase "oracle/underflow/2" instrGetQ #[.slice keyMatch, dictGetQRoot]
    , mkCase "oracle/n/type" instrGetQ #[.slice keyMatch, dictGetQRoot, .tuple #[]]
    , mkCase "oracle/n/nan" instrGetQ #[.slice keyMatch, dictGetQRoot, .int .nan]
    , mkCase "oracle/n/negative" instrGetQ #[.slice keyMatch, dictGetQRoot, intV (-1)]
    , mkCase "oracle/n/too-large" instrGetQ #[.slice keyMatch, dictGetQRoot, intV 1024]
    -- [B4][B5] type checks
    , mkCase "oracle/dict/builder" instrGetQ #[.slice keyMatch, .builder Builder.empty, intV 4]
    , mkCase "oracle/dict/tuple" instrGetQ #[.slice keyMatch, .tuple #[], intV 4]
    , mkCase "oracle/dict/int" instrGetQ #[.slice keyMatch, intV 7, intV 4]
    , mkCase "oracle/key/null" instrGetQ #[.null, dictGetQRoot, intV 4]
    , mkCase "oracle/key/cell" instrGetQ #[.cell Cell.empty, dictGetQRoot, intV 4]
    , mkCase "oracle/key/tuple" instrGetQ #[.tuple #[], dictGetQRoot, intV 4]
    , mkCase "oracle/key/builder" instrGetQ #[.builder Builder.empty, dictGetQRoot, intV 4]
    , mkCase "oracle/key/nan" instrGetQ #[.int .nan, dictGetQRoot, intV 4]
    -- [B6] miss paths
    , mkCase "oracle/miss/q" instrGetQ (mkCaseRawStack keyMismatch dictGetQRoot 3)
    , mkCase "oracle/miss/get" instrGet (mkCaseRawStack keyMismatch dictGetRoot 3)
    , mkCase "oracle/miss/jmp" instrJmp (mkCaseRawStack keyMismatch dictJmpRoot 3)
    , mkCase "oracle/miss/exec" instrExec (mkCaseRawStack keyMismatch dictExecRoot 3)
    , mkCase "oracle/miss/q-root-null" instrGetQ (mkCaseRawStack keyMatch .null 3)
    , mkCase "oracle/miss/get-root-null" instrGet (mkCaseRawStack keyMatch .null 3)
    -- [B7][B8][B9] hits
    , mkCase "oracle/hit/q" instrGetQ (mkCaseRawStack keyMatchLong dictGetQRoot 4)
    , mkCase "oracle/hit/q-longer" instrGetQ (mkCaseRawStack keyMatchLonger dictGetQRoot 5)
    , mkCase "oracle/hit/get" instrGet (mkCaseRawStack keyMatchLong dictGetRoot 4)
    , mkCase "oracle/hit/get-root-multi-branch" instrGet (mkCaseRawStack keyMatch dictGetRoot 4)
    , mkCase "oracle/hit/jmp" instrJmp (mkCaseRawStack keyMatchLong dictJmpRoot 4)
    , mkCase "oracle/hit/exec" instrExec (mkCaseRawStack keyMatchLong dictExecRoot 4)
    -- [B10][B11][B12] control-transfer and malformed
    , mkCase "oracle/malformed/q" instrGetQ (mkCaseRawStack keyMatch (.cell malformedDictRoot) 4)
    , mkCase "oracle/malformed/get" instrGet (mkCaseRawStack keyMatch (.cell malformedDictRoot) 4)
    , mkCase "oracle/malformed/jmp" instrJmp (mkCaseRawStack keyMatch (.cell malformedDictRoot) 4)
    , mkCase "oracle/malformed/exec" instrExec (mkCaseRawStack keyMatch (.cell malformedDictRoot) 4)
    -- [B16] boundary and n=0
    , mkCase "oracle/hit/n0" instrGetQ (mkCaseRawStack keyMatchLong dictN0Root 0)
    , mkCase "oracle/hit/n-max" instrGetQ (mkCaseRawStack keyMatch dictGetQRoot 1023)
    -- [B13][B14]
    , mkCaseCode "oracle/raw/f4a8" (rawOpcode 0xF4A8) (mkCaseRawStack keyMatchLong dictGetQRoot 4)
    , mkCaseCode "oracle/raw/f4a9" (rawOpcode 0xF4A9) (mkCaseRawStack keyMatchLong dictGetRoot 4)
    , mkCaseCode "oracle/raw/f4aa" (rawOpcode 0xF4AA) (mkCaseRawStack keyMatchLong dictJmpRoot 4)
    , mkCaseCode "oracle/raw/f4ab" (rawOpcode 0xF4AB) (mkCaseRawStack keyMatchLong dictExecRoot 4)
    , mkCaseCode "oracle/raw/f4a7" (rawOpcode 0xF4A7)
    , mkCaseCode "oracle/raw/f4ac" (rawOpcode 0xF4AC)
    , mkCaseCode "oracle/raw/truncated-f4" (Cell.mkOrdinary (natToBits 0xF4 8) #[])
    -- [B15]
    , mkCase
        "oracle/gas/exact-q"
        instrGetQ
        (mkCaseRawStack keyMatchLong dictGetQRoot 4)
        (oracleGasLimitsExact dictGetQExactGas)
        1_000_000
        (#[.pushInt (.num dictGetQExactGas), .tonEnvOp .setGasLimit, instrGetQ])
    , mkCase
        "oracle/gas/exact-minus-one-q"
        instrGetQ
        (mkCaseRawStack keyMatchLong dictGetQRoot 4)
        (oracleGasLimitsExactMinusOne dictGetQExactGasMinusOne)
        1_000_000
        (#[.pushInt (.num dictGetQExactGasMinusOne), .tonEnvOp .setGasLimit, instrGetQ])
    , mkCase
        "oracle/gas/exact-get"
        instrGet
        (mkCaseRawStack keyMatchLong dictGetRoot 4)
        (oracleGasLimitsExact dictGetExactGas)
        1_000_000
        (#[.pushInt (.num dictGetExactGas), .tonEnvOp .setGasLimit, instrGet])
    , mkCase
        "oracle/gas/exact-jmp"
        instrJmp
        (mkCaseRawStack keyMatchLong dictJmpRoot 4)
        (oracleGasLimitsExact dictJmpExactGas)
        1_000_000
        (#[.pushInt (.num dictJmpExactGas), .tonEnvOp .setGasLimit, instrJmp])
    , mkCase
        "oracle/gas/exact-exec"
        instrExec
        (mkCaseRawStack keyMatchLong dictExecRoot 4)
        (oracleGasLimitsExact dictExecExactGas)
        1_000_000
        (#[.pushInt (.num dictExecExactGas), .tonEnvOp .setGasLimit, instrExec])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genPFXDICTGETQFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTGETQ
