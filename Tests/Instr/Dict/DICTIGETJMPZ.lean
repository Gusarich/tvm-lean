import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETJMPZ

/-!
INSTRUCTION: DICTIGETJMPZ

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Decoder/assembler family behavior.
  - CP0 decode accepts both families masked by `0xfffc`: `0xf4a0..0xf4a3` (no Z) and `0xf4bc..0xf4bf` (Z).
  - Assembly uses base `0xf4bc` with `unsigned` and `doCall` flag bits.
  - Adjacent opcodes outside the family decode as `invOpcode`.

2. [B2] Dispatch branch.
  - `execInstrDictDictGetExec` handles `.dictGetExec`; non-matching instructions must execute `next`.

3. [B3] Runtime precondition checks.
  - Stack underflow requires 3 elements.
  - `popNatUpTo 1023` validates `n`.
  - `popMaybeCell` accepts `.null` or `.cell`.
  - `popIntFinite` validates key as finite integer.

4. [B4] Key conversion + `pushZ` behavior.
  - `dictKeyBits?` may fail for invalid key/range combinations.
  - In DICTIGETJMPZ, `pushZ=true`, so invalid conversion and dictionary misses both push the original key back.

5. [B5] Lookup outcome.
  - Dictionary hit constructs ordinary continuation and performs jump (`doCall=false`).
  - Dictionary miss has no jump and only pushes key (`pushZ=true`).

6. [B6] Malformed dictionary root handling.
  - Malformed roots trigger dictionary exceptions (`dictErr`), including root-load tracking.

7. [B7] Gas accounting.
  - base-cost success branch.
  - exact-gas-minus-one failure branch.

TOTAL BRANCHES: 7
-/

private def dictIGETJMPZId : InstrId := { name := "DICTIGETJMPZ" }

private def mkInstr (unsigned : Bool) : Instr :=
  .dictGetExec unsigned false true

private def mkInstrFull (unsigned doCall : Bool) : Instr :=
  .dictGetExec unsigned doCall true

private def defaultRetCode : Slice := Slice.ofCell Cell.empty

private def defaultCc : Continuation :=
  .ordinary defaultRetCode (.quit 0) OrdCregs.empty OrdCdata.empty

private def dispatchSentinel : Int := 12_345

private def mkDictCaseStack (idx : Value) (dict : Value) (n : Value) : Array Value :=
  #[idx, dict, n]

private def mkMethodValue : Slice :=
  mkSliceFromBits (natToBits 0xC1A5 16)

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Slice) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some kb => kb
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetSliceWithCells none keyBits value .set with
  | .ok (some root, _ok, _created, _loaded) => root
  | .ok (none, _, _, _) => panic! s!"{label}: no dict root produced"
  | .error e => panic! s!"{label}: dictSetSliceWithCells failed: {reprStr e}"

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def dictSignedHitRoot : Cell :=
  mkDictRootSlice! "dict/signed/hit" 3 4 false mkMethodValue

private def dictSignedMissRoot : Cell :=
  mkDictRootSlice! "dict/signed/miss" 9 4 false mkMethodValue

private def dictUnsignedHitRoot : Cell :=
  mkDictRootSlice! "dict/unsigned/hit" 13 4 true mkMethodValue

private def dictUnsignedMissRoot : Cell :=
  mkDictRootSlice! "dict/unsigned/miss" 2 4 true mkMethodValue

private def runDictGetJmpZDirect (stack : Array Value) (instr : Instr) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

private def runDictGetJmpZDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec instr (VM.push (intV dispatchSentinel)) stack

private def runDictGetJmpZRaw
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
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

private def expectOrdinaryMethodCont (label : String) (actual : Continuation) : IO Unit := do
  match actual with
  | .ordinary code (.quit 0) _ _ =>
      if code != mkMethodValue then
        throw (IO.userError s!"{label}: expected method continuation, got {reprStr actual}")
      else
        pure ()
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr actual}")

private def expectJumpTransfer (label : String) (st : VmState) : IO Unit := do
  expectOrdinaryMethodCont (s!"{label}/cc") st.cc
  if st.regs.c0 != Regs.initial.c0 then
    throw (IO.userError s!"{label}: expected c0 unchanged for jump, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected stack consumed, got {reprStr st.stack}")

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def dictIGETJMPZExactGas : Int :=
  computeExactGasBudget (mkInstr false)

private def dictIGETJMPZExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false)

private def mkCase
    (name : String)
    (unsigned : Bool)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[mkInstr unsigned]) : OracleCase :=
  { name := name
    instr := dictIGETJMPZId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def badValue : Value :=
  .builder Builder.empty

private def genDictIGETJMPZFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let base :=
    if shape = 0 then
      mkCase "[fuzz] hit/signed" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV 4))
    else if shape = 1 then
      mkCase "[fuzz] hit/unsigned" true (mkDictCaseStack (intV 13) (.cell dictUnsignedHitRoot) (intV 4))
    else if shape = 2 then
      mkCase "[fuzz] miss/signed" false (mkDictCaseStack (intV 9) (.cell dictSignedMissRoot) (intV 4))
    else if shape = 3 then
      mkCase "[fuzz] miss/unsigned" true (mkDictCaseStack (intV 2) (.cell dictUnsignedMissRoot) (intV 4))
    else if shape = 4 then
      mkCase "[fuzz] signed/oob-positive" false (mkDictCaseStack (intV 8) (.cell dictSignedHitRoot) (intV 4))
    else if shape = 5 then
      mkCase "[fuzz] signed/oob-negative" false (mkDictCaseStack (intV (-9)) (.cell dictSignedHitRoot) (intV 4))
    else if shape = 6 then
      mkCase "[fuzz] unsigned/oob-positive" true (mkDictCaseStack (intV 16) (.cell dictUnsignedHitRoot) (intV 4))
    else if shape = 7 then
      mkCase "[fuzz] unsigned/oob-negative" true (mkDictCaseStack (intV (-1)) (.cell dictUnsignedHitRoot) (intV 4))
    else if shape = 8 then
      mkCase "[fuzz] miss/nil-dict" false (mkDictCaseStack (intV 7) (.null) (intV 4))
    else if shape = 9 then
      mkCase "[fuzz] no-dict-unsigned" true (mkDictCaseStack (intV 10) (.null) (intV 4))
    else if shape = 10 then
      mkCase "[fuzz] n-null" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (.null))
    else if shape = 11 then
      mkCase "[fuzz] n-nan" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (.int .nan))
    else if shape = 12 then
      mkCase "[fuzz] n-negative" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV (-1)))
    else if shape = 13 then
      mkCase "[fuzz] n-too-large" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV 1024))
    else if shape = 14 then
      mkCase "[fuzz] key-null" false (mkDictCaseStack (.null) (.cell dictSignedHitRoot) (intV 4))
    else if shape = 15 then
      mkCase "[fuzz] key-nan" false (mkDictCaseStack (.int .nan) (.cell dictSignedHitRoot) (intV 4))
    else if shape = 16 then
      mkCase "[fuzz] dict-builder" false (mkDictCaseStack (intV 3) badValue (intV 4))
    else if shape = 17 then
      mkCase "[fuzz] malformed-root" false (mkDictCaseStack (intV 3) (.cell malformedDictRoot) (intV 4))
    else if shape = 18 then
      mkCase "[fuzz] gas/exact"
        false
        (mkDictCaseStack (intV 7) (.null) (intV 4))
        (oracleGasLimitsExact dictIGETJMPZExactGas)
    else
      mkCase "[fuzz] gas/exact-minus-one"
        false
        (mkDictCaseStack (intV 7) (.null) (intV 4))
        (oracleGasLimitsExactMinusOne dictIGETJMPZExactGasMinusOne)
  let (tag, rng2) := randNat rng1 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng2)

def suite : InstrSuite where
  id := dictIGETJMPZId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        match runDictGetJmpZDispatchFallback (.add) (mkDictCaseStack (intV 3) (.null) (intV 4)) with
        | .ok st =>
            if st == #[(intV dispatchSentinel)] then
              pure ()
            else
              throw (IO.userError s!"unit/dispatch/fallback: expected {reprStr #[intV dispatchSentinel]}, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"unit/dispatch/fallback: expected success, got {e}") },
    { name := "unit/decoder/decode/f4bc"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf4bc 16)
        let _ ← expectDecodeStep "unit/decoder/decode/f4bc" s (mkInstr false) 16 },
    { name := "unit/decoder/decode/f4bd"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf4bd 16)
        let _ ← expectDecodeStep "unit/decoder/decode/f4bd" s (mkInstr true) 16 },
    { name := "unit/decoder/decode/f4be"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf4be 16)
        let _ ← expectDecodeStep "unit/decoder/decode/f4be" s (mkInstrFull false true) 16 },
    { name := "unit/decoder/decode/f4bf"
      run := do
        let s : Slice := mkSliceFromBits (natToBits 0xf4bf 16)
        let _ ← expectDecodeStep "unit/decoder/decode/f4bf" s (mkInstrFull true true) 16 },
    { name := "unit/decoder/decode/invalid-neighbor-low"
      run := do
        expectDecodeInvOpcode "unit/decoder/decode/invalid-neighbor-low" 0xf4a4 },
    { name := "unit/decoder/decode/invalid-neighbor-high"
      run := do
        expectDecodeInvOpcode "unit/decoder/decode/invalid-neighbor-high" 0xf4c0 },
    { name := "unit/asm/encode/f4bc"
      run := do
        match assembleCp0 [mkInstr false] with
        | .ok c0 =>
            if c0.bits == natToBits 0xf4bc 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bc: expected bits 0xf4bc")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bc: expected success, got {e}") },
    { name := "unit/asm/encode/f4bd"
      run := do
        match assembleCp0 [mkInstr true] with
        | .ok c0 =>
            if c0.bits == natToBits 0xf4bd 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bd: expected bits 0xf4bd")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bd: expected success, got {e}") },
    { name := "unit/asm/encode/f4be"
      run := do
        match assembleCp0 [mkInstrFull false true] with
        | .ok c0 =>
            if c0.bits == natToBits 0xf4be 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4be: expected bits 0xf4be")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4be: expected success, got {e}") },
    { name := "unit/asm/encode/f4bf"
      run := do
        match assembleCp0 [mkInstrFull true true] with
        | .ok c0 =>
            if c0.bits == natToBits 0xf4bf 16 then
              pure ()
            else
              throw (IO.userError "unit/asm/encode/f4bf: expected bits 0xf4bf")
        | .error e => throw (IO.userError s!"unit/asm/encode/f4bf: expected success, got {e}") },
    { name := "unit/control/jump/signed"
      run := do
        let st ←
          expectRawOk "unit/control/jump/signed"
            (runDictGetJmpZRaw (mkInstr false) (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV 4)))
        expectJumpTransfer "unit/control/jump/signed" st },
    { name := "unit/control/jump/unsigned"
      run := do
        let st ←
          expectRawOk "unit/control/jump/unsigned"
            (runDictGetJmpZRaw (mkInstr true) (mkDictCaseStack (intV 13) (.cell dictUnsignedHitRoot) (intV 4)))
        expectJumpTransfer "unit/control/jump/unsigned" st },
    { name := "unit/stack/signed/miss/pushz"
      run := do
        expectOkStack "unit/stack/signed/miss/pushz"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 7) (.cell dictSignedMissRoot) (intV 4)) (mkInstr false)) #[intV 7] },
    { name := "unit/stack/unsigned/miss/pushz"
      run := do
        expectOkStack "unit/stack/unsigned/miss/pushz"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 10) (.cell dictUnsignedMissRoot) (intV 4)) (mkInstr true)) #[intV 10] },
    { name := "unit/stack/signed/miss/pushz-tail"
      run := do
        expectOkStack "unit/stack/signed/miss/pushz-tail"
          (runDictGetJmpZDirect #[intV 99, intV 7, (.cell dictSignedMissRoot), intV 4] (mkInstr false))
          #[intV 99, intV 7] },
    { name := "unit/stack/unsigned/miss/pushz-tail"
      run := do
        expectOkStack "unit/stack/unsigned/miss/pushz-tail"
          (runDictGetJmpZDirect #[intV 42, intV 10, (.cell dictUnsignedMissRoot), intV 4] (mkInstr true))
          #[intV 42, intV 10] },
    { name := "unit/stack/signed/key-oob/pushz"
      run := do
        expectOkStack "unit/stack/signed/key-oob/pushz"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 8) (.cell dictSignedHitRoot) (intV 4)) (mkInstr false))
          #[intV 8] },
    { name := "unit/stack/unsigned/key-oob/pushz"
      run := do
        expectOkStack "unit/stack/unsigned/key-oob/pushz"
          (runDictGetJmpZDirect (mkDictCaseStack (intV (-1)) (.cell dictUnsignedHitRoot) (intV 4)) (mkInstr true))
          #[intV (-1)] },
    { name := "unit/errors/underflow/empty"
      run := do
        expectErr "unit/errors/underflow/empty" (runDictGetJmpZDirect #[] (mkInstr false)) .stkUnd },
    { name := "unit/errors/underflow/one"
      run := do
        expectErr "unit/errors/underflow/one" (runDictGetJmpZDirect #[.null] (mkInstr false)) .stkUnd },
    { name := "unit/errors/underflow/two"
      run := do
        expectErr "unit/errors/underflow/two" (runDictGetJmpZDirect #[.null, .null] (mkInstr false)) .stkUnd },
    { name := "unit/errors/n-null"
      run := do
        expectErr "unit/errors/n-null"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 3) (.null) (.null)) (mkInstr false)) .typeChk },
    { name := "unit/errors/n-nan"
      run := do
        expectErr "unit/errors/n-nan"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 3) (.null) (.int .nan)) (mkInstr false)) .rangeChk },
    { name := "unit/errors/n-negative"
      run := do
        expectErr "unit/errors/n-negative"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 3) (.null) (intV (-1))) (mkInstr false)) .rangeChk },
    { name := "unit/errors/n-too-large"
      run := do
        expectErr "unit/errors/n-too-large"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 3) (.null) (intV 1024)) (mkInstr false)) .rangeChk },
    { name := "unit/errors/key-null"
      run := do
        expectErr "unit/errors/key-null"
          (runDictGetJmpZDirect (mkDictCaseStack (.null) (.null) (intV 4)) (mkInstr false)) .typeChk },
    { name := "unit/errors/key-nan"
      run := do
        expectErr "unit/errors/key-nan"
          (runDictGetJmpZDirect (mkDictCaseStack (.int .nan) (.null) (intV 4)) (mkInstr false)) .intOv },
    { name := "unit/errors/dict-builder"
      run := do
        expectErr "unit/errors/dict-builder"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 3) badValue (intV 4)) (mkInstr false)) .typeChk },
    { name := "unit/errors/malformed-root"
      run := do
        let _ ← expectRawErr "unit/errors/malformed-root"
          (runDictGetJmpZRaw (mkInstr false) (mkDictCaseStack (intV 3) (.cell malformedDictRoot) (intV 4))
          ) .dictErr
        pure () },
    { name := "unit/gas/exact-success"
      run := do
        expectOkStack "unit/gas/exact-success"
          (runDictGetJmpZDirect (mkDictCaseStack (intV 7) (.null) (intV 4)) (mkInstr false)) #[]
    }
  ]
  oracle := #[
    -- [B5] direct jump path on dictionary hit.
    mkCase "[B5] hit/signed/jump" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B5] hit/unsigned/jump" true (mkDictCaseStack (intV 13) (.cell dictUnsignedHitRoot) (intV 4)),

    -- [B4] misses and oob keys under pushZ.
    mkCase "[B4] miss/signed" false (mkDictCaseStack (intV 7) (.cell dictSignedMissRoot) (intV 4)),
    mkCase "[B4] miss/unsigned" true (mkDictCaseStack (intV 10) (.cell dictUnsignedMissRoot) (intV 4)),
    mkCase "[B4] miss/signed/tail" false (#[(intV 88), (intV 7), (.cell dictSignedMissRoot), intV 4]),
    mkCase "[B4] miss/unsigned/tail" true (#[(intV 99), (intV 10), (.cell dictUnsignedMissRoot), intV 4]),
    mkCase "[B4] signed/oob-positive" false (mkDictCaseStack (intV 8) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B4] signed/oob-negative" false (mkDictCaseStack (intV (-9)) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B4] signed/n-zero-oob" false (mkDictCaseStack (intV 1) (.cell dictSignedMissRoot) (intV 0)),
    mkCase "[B4] unsigned/oob-positive" true (mkDictCaseStack (intV 16) (.cell dictUnsignedHitRoot) (intV 4)),
    mkCase "[B4] unsigned/oob-negative" true (mkDictCaseStack (intV (-1)) (.cell dictUnsignedHitRoot) (intV 4)),
    mkCase "[B4] unsigned/n-zero-oob" true (mkDictCaseStack (intV 1) (.cell dictUnsignedMissRoot) (intV 0)),

    -- [B3] runtime argument shape and type errors.
    mkCase "[B3] n-null" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (.null)),
    mkCase "[B3] n-nan" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (.int .nan)),
    mkCase "[B3] n-negative" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV (-1))),
    mkCase "[B3] n-too-large" false (mkDictCaseStack (intV 3) (.cell dictSignedHitRoot) (intV 1024)),
    mkCase "[B3] key-null" false (mkDictCaseStack (.null) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B3] key-cell" false (mkDictCaseStack (.cell dictSignedHitRoot) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B3] key-builder" false (mkDictCaseStack (.builder Builder.empty) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B3] key-nan" false (mkDictCaseStack (.int .nan) (.cell dictSignedHitRoot) (intV 4)),
    mkCase "[B3] dict-builder" false (mkDictCaseStack (intV 3) badValue (intV 4)),
    mkCase "[B3] dict-cellslice" false (mkDictCaseStack (intV 3) (.slice mkMethodValue) (intV 4)),
    mkCase "[B3] dict-null-tail" false (#[.cell dictSignedMissRoot, (intV 7), (.null), intV 4]),

    -- [B6] malformed dictionary root.
    mkCase "[B6] malformed-root/miss" false (mkDictCaseStack (intV 3) (.cell malformedDictRoot) (intV 4)),
    mkCase "[B6] malformed-root/miss/tail" false (#[intV 12, (intV 3), (.cell malformedDictRoot), intV 4]),
    mkCase "[B6] malformed-root/hit" false (mkDictCaseStack (intV 3) (.cell malformedDictRoot) (intV 4)),

    -- [B3] underflow and near-underflow.
    mkCase "[B3] underflow-empty" false #[],
    mkCase "[B3] underflow-one" false (#[(intV 4)]),
    mkCase "[B3] underflow-two" false (#[(intV 4), (.cell dictSignedHitRoot)]),
    mkCase "[B3] underflow-tail" false (#[(intV 77), (intV 3)]),

    -- [B7] gas accounting.
    mkCase "[B7] gas/exact" false (mkDictCaseStack (intV 7) (.null) (intV 4))
      (oracleGasLimitsExact dictIGETJMPZExactGas),
    mkCase "[B7] gas/exact-minus-one" false (mkDictCaseStack (intV 7) (.null) (intV 4))
      (oracleGasLimitsExactMinusOne dictIGETJMPZExactGasMinusOne)
  ]
  fuzz := #[
    { seed := 2026_02_13
      count := 500
      gen := genDictIGETJMPZFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETJMPZ
