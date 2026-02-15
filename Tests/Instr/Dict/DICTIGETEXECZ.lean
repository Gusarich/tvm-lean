import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETEXECZ

/-!
INSTRUCTION: DICTIGETEXECZ

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Runtime dispatch path.
   - `execInstrDictDictGetExec` handles only `.dictGetExec`; all other instructions must
     flow to `next`.

2. [B2] Runtime preamble and operand order.
   - `checkUnderflow 3` is required.
   - The runtime pops `n`, then `dict`, then `idx` (via `popNatUpTo`, `popMaybeCell`, `popIntFinite`).
   - Any underflow on these pops produces `.stkUnd`.

3. [B3] `n` validation.
   - `popNatUpTo 1023` allows only int-like naturals in range `[0, 1023]`.
   - Non-int `n` produces `.typeChk`, while NaN/negative/out-of-range produces `.rangeChk`.

4. [B4] Dictionary argument validation.
   - `popMaybeCell` accepts `.null` and `.cell`.
   - Any other value produces `.typeChk`.

5. [B5] Signed key conversion and miss classification.
   - `popIntFinite` accepts integer values and maps NaN to `.intOv`.
   - `dictKeyBits?` with `unsigned = false` performs signed key encoding.
   - Keys outside signed range for a given `n` return `none` and follow miss path.

6. [B6] Miss branch (`pushZ = true`).
   - Null root, absent key, key-conversion failure and dictionary traversal miss all push the original `idx`.
   - Prefix stack tail must be preserved and only `idx` is appended.

7. [B7] Hit branch with `doCall = true`.
   - On key hit, lookup returns an ordinary continuation and execution uses `callTo`.
   - `c0` must be re-pointed to the current continuation return continuation.
   - Existing stack prefix must be preserved.

8. [B8] Malformed dictionary traversal.
   - Traversal/build errors on malformed root return `.dictErr`.

9. [B9] Assembler encoding boundaries.
   - `unsigned=false, doCall=true, pushZ=true` encodes to opcode `0xf4be`.
   - `assemble` for this constructor has no out-of-range numeric arguments to reject.

10. [B10] Decoder behavior and aliasing.
   - `decode` accepts family aliases by mask `0xfffc`, so `0xf4a0..0xf4a3` and `0xf4bc..0xf4bf` are all dictionary get-exec/jmp variants.
   - Decode of `0xf4bc` and `0xf4bf` produce sibling variants (same family).
   - Invalid opcodes just outside the families must decode as `invOpcode`.

11. [B11] Gas accounting.
   - Base cost only for this instruction family variant.
   - Exact-gas-success and exact-gas-minus-one-failure paths must be validated.

TOTAL BRANCHES: 11

Each oracle test below is tagged [B#] to the branch(es) it covers.
Any branch not covered by oracle tests should be reached by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "DICTIGETEXECZ" }

private def instr : Instr := .dictGetExec false true true

private def dispatchSentinel : Int := 12_345

private def markerSlice (marker : Nat) : Slice :=
  mkSliceFromBits (natToBits marker 16)

private def jumpTargetSlice : Slice := markerSlice 0xBEEF

private def valueA : Slice := markerSlice 0xA111
private def valueB : Slice := markerSlice 0xB222
private def valueC : Slice := markerSlice 0xC333
private def valueD : Slice := markerSlice 0xD444
private def valueE : Slice := markerSlice 0xE555
private def valueF : Slice := markerSlice 0xF666
private def value0 : Slice := markerSlice 0x0000

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for pair in pairs do
      let keyBits : BitString :=
        match dictKeyBits? pair.1 n false with
        | some bits => bits
        | none => panic! s!"{label}: unsupported signed key ({pair.1}) for n={n}"
      match dictSetSliceWithCells root keyBits pair.2 .set with
      | .ok (some next, _ok, _created, _loaded) =>
          root := next
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty dict while building"
      | .error e =>
          panic! s!"{label}: dict set failed ({reprStr e})"
    match root with
    | some r => r
    | none => panic! s!"{label}: failed to build dictionary"

private def dictSigned4HitRoot : Cell :=
  mkDictFromPairs "dictSigned4HitRoot" 4 #[
    (3, jumpTargetSlice),
    (-2, valueA),
    (-8, valueB),
    (7, valueC)
  ]

private def dictSigned4MissRoot : Cell :=
  mkDictFromPairs "dictSigned4MissRoot" 4 #[
    (-2, valueA),
    (2, valueB),
    (7, valueC)
  ]

private def dictSigned4BoundaryRoot : Cell :=
  mkDictFromPairs "dictSigned4BoundaryRoot" 4 #[
    (-8, valueD),
    (7, valueE),
    (0, valueF)
  ]

private def dictSigned1Root : Cell :=
  mkDictFromPairs "dictSigned1Root" 1 #[
    (-1, valueA),
    (0, valueB)
  ]

private def dictSigned0Root : Cell :=
  mkDictFromPairs "dictSigned0Root" 0 #[
    (0, value0)
  ]

private def malformedDictRoot : Cell :=
  Cell.mkOrdinary (natToBits 0b1010 4) #[]

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def sentinelCc : Continuation :=
  .ordinary (Slice.ofCell (Cell.mkOrdinary (natToBits 0xFACE 16) #[])) (.quit 99) OrdCregs.empty OrdCdata.empty

private def sentinelC0 : Continuation := .quit 17

private def regsWithSentinelC0 : Regs :=
  { Regs.initial with c0 := sentinelC0 }

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ =>
      .quit 0

private def mkDictCaseStack (idx : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV idx, dict, intV n]

private def runDICTIGETEXECZDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

private def runDICTIGETEXECZFallback (initial : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec initial (VM.push (intV dispatchSentinel)) stack

private def runDICTIGETEXECZRaw
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

private def expectErrDictLike
    (label : String)
    (res : Except Excno (Array Value)) : IO Unit := do
  match res with
  | .error .dictErr => pure ()
  | .error .cellUnd => pure ()
  | .error e => throw (IO.userError s!"{label}: expected dictErr/cellUnd, got {e}")
  | .ok st => throw (IO.userError s!"{label}: expected dictErr/cellUnd, got success {reprStr st}")

private def expectRawErrDictLike
    (label : String)
    (res : Except Excno Unit × VmState) : IO VmState := do
  let (r, st) := res
  match r with
  | .error .dictErr => pure st
  | .error .cellUnd => pure st
  | .error e => throw (IO.userError s!"{label}: expected dictErr/cellUnd, got {e}")
  | .ok _ => throw (IO.userError s!"{label}: expected dictErr/cellUnd, got success")

private def expectCallTransfer
    (label : String)
    (target : Slice)
    (oldCc : Continuation)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  let expectedC0 := callReturnFromCc oldCc oldC0
  match st.cc with
  | .ordinary code (.quit 0) _ _ =>
      if code.bitsRemaining + code.refsRemaining = 0 then
        throw (IO.userError s!"{label}: expected non-empty cc code, got {reprStr code}")
  | _ =>
      throw (IO.userError s!"{label}: expected ordinary continuation after call")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected regs.c0 {reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack on miss? got {reprStr st.stack}")

private def rawF4BE : Cell := Cell.mkOrdinary (natToBits 0xF4BE 16) #[]
private def rawF4BF : Cell := Cell.mkOrdinary (natToBits 0xF4BF 16) #[]
private def rawF4BD : Cell := Cell.mkOrdinary (natToBits 0xF4BD 16) #[]
private def rawF4A2 : Cell := Cell.mkOrdinary (natToBits 0xF4A2 16) #[]
private def rawF4A0 : Cell := Cell.mkOrdinary (natToBits 0xF4A0 16) #[]
private def rawF4A4 : Cell := Cell.mkOrdinary (natToBits 0xF4A4 16) #[]
private def rawF4C0 : Cell := Cell.mkOrdinary (natToBits 0xF4C0 16) #[]

private def expectDecodeStepExact (label : String) (opcode : Nat) (expected : Instr) : IO Unit := do
  let c : Cell ←
    match assembleCp0 [expected] with
    | .ok cell => pure cell
    | .error e => throw (IO.userError s!"{label}: assemble failed ({reprStr e})")
  if c.bits != natToBits opcode 16 then
    throw (IO.userError s!"{label}: expected opcode 0x{opcode}, got {c.bits}")
  let _ ← expectDecodeStep label (Slice.ofCell c) expected 16

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell (Cell.mkOrdinary (natToBits opcode 16) #[])) with
  | .ok _ => throw (IO.userError s!"{label}: expected invOpcode at opcode {opcode}")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def dictIGETEXECZGas : Int := computeExactGasBudget instr
private def dictIGETEXECZGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictIGETEXECZGas
private def gasMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictIGETEXECZGasMinusOne

private def mkCase
    (name : String)
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
    (code : Cell)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDICTIGETEXECZFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let case0 : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/0" #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/1" #[]
    else if shape = 2 then
      mkCase "fuzz/underflow/2" #[.null]
    else if shape = 3 then
      mkCase "fuzz/err/n-type" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) (Int.ofNat 4) |>.set! 2 (.tuple #[]))
    else if shape = 4 then
      mkCase "fuzz/err/n-nan" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 2 (.int .nan))
    else if shape = 5 then
      mkCase "fuzz/err/n-negative" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) (-1))
    else if shape = 6 then
      mkCase "fuzz/err/n-too-large" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 1024)
    else if shape = 7 then
      mkCase "fuzz/err/dict-builder" (mkDictCaseStack 3 (.builder Builder.empty) 4)
    else if shape = 8 then
      mkCase "fuzz/err/dict-tuple" (mkDictCaseStack 3 (.tuple #[]) 4)
    else if shape = 9 then
      mkCase "fuzz/err/key-null" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.null))
    else if shape = 10 then
      mkCase "fuzz/err/key-cell" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.cell Cell.empty))
    else if shape = 11 then
      mkCase "fuzz/err/key-nan" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.int .nan))
    else if shape = 12 then
      mkCase "fuzz/miss/oob-pos" (mkDictCaseStack 8 (.cell dictSigned4MissRoot) 4)
    else if shape = 13 then
      mkCase "fuzz/miss/oob-neg" (mkDictCaseStack (-9) (.cell dictSigned4MissRoot) 4)
    else if shape = 14 then
      mkCase "fuzz/miss/null-root" (mkDictCaseStack 3 (.null) 4)
    else if shape = 15 then
      mkCase "fuzz/miss/in-tree" (mkDictCaseStack 2 (.cell dictSigned4MissRoot) 4)
    else if shape = 16 then
      mkCase "fuzz/miss/prefix-preserved" (#[(intV 77), intV 8, (.cell dictSigned4MissRoot), intV 4])
    else if shape = 17 then
      mkCase "fuzz/miss/n0" (mkDictCaseStack 1 (.cell dictSigned0Root) 0)
    else if shape = 18 then
      mkCase "fuzz/miss/n1" (mkDictCaseStack 1 (.cell dictSigned1Root) 1)
    else if shape = 19 then
      mkCase "fuzz/hit/basic" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
    else if shape = 20 then
      mkCase "fuzz/hit/prefix" (#[(intV 77), intV 3, (.cell dictSigned4HitRoot), intV 4])
    else if shape = 21 then
      mkCase "fuzz/hit/boundary-max" (mkDictCaseStack 7 (.cell dictSigned4BoundaryRoot) 4)
    else if shape = 22 then
      mkCase "fuzz/hit/boundary-min" (mkDictCaseStack (-8) (.cell dictSigned4BoundaryRoot) 4)
    else if shape = 23 then
      mkCase "fuzz/hit/n1-max" (mkDictCaseStack 0 (.cell dictSigned1Root) 1)
    else if shape = 24 then
      mkCase "fuzz/hit/n1-min" (mkDictCaseStack (-1) (.cell dictSigned1Root) 1)
    else if shape = 25 then
      mkCase "fuzz/hit/n0" (mkDictCaseStack 0 (.cell dictSigned0Root) 0)
    else if shape = 26 then
      mkCase
        "fuzz/malformed-root"
        (mkDictCaseStack 3 (.cell malformedDictRoot) 4)
    else if shape = 27 then
      mkCase
        "fuzz/malformed-root-prefix"
        (#[(intV 77), intV 3, (.cell malformedDictRoot), intV 4])
    else if shape = 28 then
      mkCase
        "fuzz/gas/exact"
        (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
        gasExact
        1_000_000
        (#[.pushInt (.num dictIGETEXECZGas), .tonEnvOp .setGasLimit, instr])
    else if shape = 29 then
      mkCase
        "fuzz/gas/exact-minus-one"
        (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
        gasMinusOne
        1_000_000
        (#[.pushInt (.num dictIGETEXECZGasMinusOne), .tonEnvOp .setGasLimit, instr])
    else if shape = 30 then
      mkCaseCode "fuzz/raw/f4be" rawF4BE
    else if shape = 31 then
      mkCaseCode "fuzz/raw/f4bd" rawF4BD
    else if shape = 32 then
      mkCaseCode "fuzz/raw/f4bf" rawF4BF
    else if shape = 33 then
      mkCaseCode "fuzz/raw/f4a2" rawF4A2
    else if shape = 34 then
      mkCaseCode "fuzz/raw/f4a0" rawF4A0
    else if shape = 35 then
      mkCaseCode "fuzz/raw/invalid-f4a4" rawF4A4
    else if shape = 36 then
      mkCaseCode "fuzz/raw/invalid-f4c0" rawF4C0
    else if shape = 37 then
      mkCase
        "fuzz/prefix-hit-call"
        (#[intV 99, intV 3, (.cell dictSigned4HitRoot), intV 4]) -- preserve prefix on hit
    else if shape = 38 then
      mkCase
        "fuzz/prefix-miss-call"
        (#[intV 99, intV 8, (.cell dictSigned4MissRoot), intV 4]) -- preserve prefix on miss
    else if shape = 39 then
      mkCase
        "fuzz/random-hit"
        (#[intV 3, (.cell dictSigned4HitRoot), intV 4])
    else
      mkCase "fuzz/random" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng2)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let init : Array Value := mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4
        let stNonMatch := runDICTIGETEXECZFallback .add init
        expectOkStack "unit/dispatch/fallback/non-match" stNonMatch #[intV 3, .cell dictSigned4HitRoot, intV 4, intV dispatchSentinel]
        let stMatch := runDICTIGETEXECZFallback instr init
        expectOkStack "unit/dispatch/fallback/match" stMatch #[] },
    { name := "unit/asm/encode-decode" -- [B9][B10]
      run := do
        expectDecodeStepExact "unit/asm" 0xF4BE instr
        match assembleCp0 [instr] with
        | .ok bits =>
            if bits.bits != natToBits 0xF4BE 16 then
              throw (IO.userError "unit/asm: unexpected bits")
        | .error e => throw (IO.userError s!"unit/asm: {reprStr e}")
        let _ ← expectDecodeStep "unit/decoder/f4be" (Slice.ofCell rawF4BE) instr 16
        expectDecodeInvOpcode "unit/decoder/f4a4" 0xF4A4
        expectDecodeInvOpcode "unit/decoder/f4c0" 0xF4C0 },
    { name := "unit/errors/underflow" -- [B2]
      run := do
        expectErr "underflow-empty" (runDICTIGETEXECZDirect #[]) .stkUnd
        expectErr "underflow-one" (runDICTIGETEXECZDirect #[.null]) .stkUnd
        expectErr "underflow-two" (runDICTIGETEXECZDirect #[.null, (.cell dictSigned4HitRoot)]) .stkUnd },
    { name := "unit/errors/n-operand" -- [B3]
      run := do
        expectErr
          "n-not-int"
          (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) (Int.ofNat 0) |>.set! 2 (.tuple #[])))
          .typeChk
        expectErr
          "n-nan"
          (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 2 (.int .nan)))
          .rangeChk
        expectErr "n-negative" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) (-1))) .rangeChk
        expectErr "n-too-large" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 1024)) .rangeChk },
    { name := "unit/errors/dict-key" -- [B4][B5]
      run := do
        expectErr "dict-builder" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.builder Builder.empty) 4)) .typeChk
        expectErr "dict-tuple" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.tuple #[]) 4)) .typeChk
        expectErr "key-null" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.null))) .typeChk
        expectErr "key-cell" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.cell Cell.empty))) .typeChk
        expectErr "key-nan" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.int .nan))) .intOv },
    { name := "unit/exec/miss-paths" -- [B6]
      run := do
        expectOkStack
          "miss/oob-pos"
          (runDICTIGETEXECZDirect (mkDictCaseStack 8 (.cell dictSigned4MissRoot) 4))
          #[intV 8]
        expectOkStack
          "miss/oob-neg"
          (runDICTIGETEXECZDirect (mkDictCaseStack (-9) (.cell dictSigned4MissRoot) 4))
          #[intV (-9)]
        expectOkStack
          "miss/null-root"
          (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.null) 4))
          #[intV 3]
        expectOkStack
          "miss/prefix-preserved"
          (runDICTIGETEXECZDirect (#[(intV 77), intV 16, (.cell dictSigned4MissRoot), intV 4]))
          #[intV 77, intV 16] },
    { name := "unit/exec/hit-call" -- [B7]
      run := do
        expectOkStack "hit/basic" (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)) #[]
        expectOkStack "hit/prefix" (runDICTIGETEXECZDirect (#[(intV 77), intV 3, (.cell dictSigned4HitRoot), intV 4])) #[intV 77] },
    { name := "unit/errors/malformed-root" -- [B8]
      run := do
        expectErrDictLike
          "malformed-root"
          (runDICTIGETEXECZDirect (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
        let _ ←
          expectRawErrDictLike
            "malformed-root/raw"
            (runDICTIGETEXECZRaw (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
        pure () },
    { name := "unit/raw/call-transfer" -- [B7]
      run := do
        let st ←
          expectRawOk
            "raw/call-transfer"
            (runDICTIGETEXECZRaw (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4) regsWithSentinelC0 sentinelCc)
        expectCallTransfer "raw/call-transfer" jumpTargetSlice sentinelCc sentinelC0 st }
  ]
  oracle := #[
    mkCase "oracle/dispatch/non-match" #[] , -- [B1]
    mkCase "oracle/dispatch/match" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4), -- [B1]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[.null], -- [B2]
    mkCase "oracle/underflow/two" #[.null, (.cell dictSigned4HitRoot)], -- [B2]
    mkCase "oracle/n/not-int" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 2 (.tuple #[])), -- [B3]
    mkCase "oracle/n/nan" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 2 (.int .nan)), -- [B3]
    mkCase "oracle/n/negative" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) (-1)), -- [B3]
    mkCase "oracle/n/too-large" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 1024), -- [B3]
    mkCase "oracle/dict/builder" (mkDictCaseStack 3 (.builder Builder.empty) 4), -- [B4]
    mkCase "oracle/dict/tuple" (mkDictCaseStack 3 (.tuple #[]) 4), -- [B4]
    mkCase "oracle/key/null" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.null)), -- [B5]
    mkCase "oracle/key/cell" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.cell Cell.empty)), -- [B5]
    mkCase "oracle/key/nan" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4 |>.set! 0 (.int .nan)), -- [B5]
    mkCase "oracle/miss/oob-positive" (mkDictCaseStack 8 (.cell dictSigned4MissRoot) 4), -- [B6]
    mkCase "oracle/miss/oob-negative" (mkDictCaseStack (-9) (.cell dictSigned4MissRoot) 4), -- [B6]
    mkCase "oracle/miss/in-tree" (mkDictCaseStack 2 (.cell dictSigned4MissRoot) 4), -- [B6]
    mkCase "oracle/miss/null-root" (mkDictCaseStack 3 (.null) 4), -- [B6]
    mkCase "oracle/miss/prefix-preserved" (#[(intV 77), intV 16, (.cell dictSigned4MissRoot), intV 4]), -- [B6]
    mkCase "oracle/miss/n0-empty" (mkDictCaseStack 1 (.cell dictSigned0Root) 0), -- [B6]
    mkCase "oracle/miss/n1-empty" (mkDictCaseStack 1 (.cell dictSigned1Root) 1), -- [B6]
    mkCase "oracle/hit/basic-call" (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4), -- [B7]
    mkCase "oracle/hit/prefix-call" (#[(intV 77), intV 3, (.cell dictSigned4HitRoot), intV 4]), -- [B7]
    mkCase "oracle/hit/boundary-max" (mkDictCaseStack 7 (.cell dictSigned4BoundaryRoot) 4), -- [B7]
    mkCase "oracle/hit/boundary-min" (mkDictCaseStack (-8) (.cell dictSigned4BoundaryRoot) 4), -- [B7]
    mkCase "oracle/hit/n1-zero" (mkDictCaseStack 0 (.cell dictSigned1Root) 1), -- [B7]
    mkCase "oracle/hit/n1-minus-one" (mkDictCaseStack (-1) (.cell dictSigned1Root) 1), -- [B7]
    mkCase "oracle/hit/n0" (mkDictCaseStack 0 (.cell dictSigned0Root) 0), -- [B7]
    mkCase "oracle/malformed-root" (mkDictCaseStack 3 (.cell malformedDictRoot) 4), -- [B8]
    mkCase "oracle/malformed-root-prefix" (#[(intV 77), intV 3, (.cell malformedDictRoot), intV 4]), -- [B8]
    mkCaseCode "oracle/raw/f4be" rawF4BE, -- [B9][B10]
    mkCaseCode "oracle/raw/f4bf-sibling" rawF4BF, -- [B10]
    mkCaseCode "oracle/raw/f4bd-sibling" rawF4BD, -- [B10]
    mkCaseCode "oracle/raw/f4a2-sibling" rawF4A2, -- [B10]
    mkCaseCode "oracle/raw/f4a0-sibling" rawF4A0, -- [B10]
    mkCaseCode "oracle/raw/invalid-f4a4" rawF4A4, -- [B10]
    mkCaseCode "oracle/raw/invalid-f4c0" rawF4C0, -- [B10]
    mkCase
      "oracle/gas/exact"
      (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
      gasExact
      1_000_000
      (#[.pushInt (.num dictIGETEXECZGas), .tonEnvOp .setGasLimit, instr]), -- [B11]
    mkCase
      "oracle/gas/exact-minus-one"
      (mkDictCaseStack 3 (.cell dictSigned4HitRoot) 4)
      gasMinusOne
      1_000_000
      (#[.pushInt (.num dictIGETEXECZGasMinusOne), .tonEnvOp .setGasLimit, instr]) -- [B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDICTIGETEXECZFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETEXECZ
