import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETEXECZ

/-!
INSTRUCTION: DICTUGETEXECZ

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictDictGet` matches only `.dictGetExec`; all other instructions forward to `next`.

2. [B2] Stack arity and operand order.
   - `checkUnderflow 3` is enforced, then pops `n`, `dict`, `idx` in that order.

3. [B3] `n` validation (`popNatUpTo 1023`).
   - `.typeChk` for non-int.
   - `.rangeChk` for NaN, negative, and out-of-range (`> 1023`) values.

4. [B4] Dictionary argument handling.
   - `popMaybeCell` accepts only `null` and `cell`; all other values raise `.typeChk`.

5. [B5] Key parsing and conversion.
   - `popIntFinite` raises `.typeChk` for non-int and `.intOv` for NaN.
   - `dictKeyBits?` for unsigned keys returns `none` for out-of-range/invalid keys, which is a miss path.

6. [B6] Miss path with `pushZ = true`.
   - Any miss (null dict, conversion failure, or absent key) pushes the original `idx` back and returns.

7. [B7] Lookup hit + control transfer with `doCall = true`.
   - Valid key+present value installs continuation and performs `callTo`.

8. [B8] Malformed dictionary traversal.
   - Malformed root or traversal failures propagate `.dictErr`.

9. [B9] Assembler encoding.
   - `(unsigned=true, doCall=true, pushZ=true)` encodes to `0xf4bf` (`0xf4bc + 3`).
   - No other parameter mix is represented by this file’s instruction identity.

10. [B10] Decoder boundaries.
    - `decodeCp0WithBits 0xf4bf` yields `.dictGetExec true true true`.
    - Nearby masked-opcodes outside this family are invalid (`invOpcode`) and exercise aliasing boundaries.

11. [B11] Gas accounting.
    - No branch-specific variable gas is modeled here; verify exact base-cost success and exact-minus-one failure paths.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def dictUGETEXECZId : InstrId := { name := "DICTUGETEXECZ" }

private def instr : Instr := .dictGetExec true true true

private def dispatchSentinel : Int := 12_345

private def markerSlice (marker : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits marker 16) #[])

private def jumpTargetSlice : Slice := markerSlice 0xABCD

private def mkDictFromPairs (label : String) (n : Nat) (pairs : Array (Int × Slice)) : Cell :=
  let rootOpt : Option Cell :=
    pairs.foldl
      (fun st pair =>
        let keyBits : BitString :=
          match dictKeyBits? pair.1 n true with
          | some bits => bits
          | none => panic! s!"{label}: unsupported key {pair.1} for n={n}"
        match st with
        | some root =>
            match dictSetSliceWithCells (some root) keyBits pair.2 .set with
            | .ok (some next, _, _, _) => some next
            | _ => none
        | none =>
            match dictSetSliceWithCells none keyBits pair.2 .set with
            | .ok (some root, _, _, _) => some root
            | _ => none)
      none
  match rootOpt with
  | some root => root
  | none => panic! s!"{label}: failed to build dictionary"

private def dictUnsigned4HitRoot : Cell :=
  mkDictFromPairs "dictUnsigned4HitRoot" 4 #[(3, jumpTargetSlice)]

private def dictUnsigned4MissRoot : Cell :=
  mkDictFromPairs "dictUnsigned4MissRoot" 4 #[(2, markerSlice 0xBBBB)]

private def dictUnsigned4Root : Cell :=
  mkDictFromPairs "dictUnsigned4Root" 4 #[(2, markerSlice 0xBBBB), (3, jumpTargetSlice)]

private def dictUnsignedN0Root : Cell :=
  mkDictFromPairs "dictUnsignedN0Root" 0 #[(0, markerSlice 0xC000)]

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 0b10 2) #[]

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
  | _ => .quit 0

private def mkDictCaseStack (idx : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV idx, dict, intV n]

private def runDictUGETEXECZDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

private def runDictUGETEXECZDispatchFallback (initial : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec initial (VM.push (intV dispatchSentinel)) stack

private def runDictUGETEXECZRaw
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
        throw (IO.userError s!"{label}: expected cc code {reprStr target}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation")
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected regs.c0 {reprStr expectedC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after call, got {reprStr st.stack}")

private def rawF4bf : Cell := Cell.mkOrdinary (natToBits 0xf4bf 16) #[]
private def rawF4be : Cell := Cell.mkOrdinary (natToBits 0xf4be 16) #[]
private def rawF4a0 : Cell := Cell.mkOrdinary (natToBits 0xf4a0 16) #[]
private def rawF4a4 : Cell := Cell.mkOrdinary (natToBits 0xf4a4 16) #[]
private def rawF4b0 : Cell := Cell.mkOrdinary (natToBits 0xf4b0 16) #[]
private def rawF4c0 : Cell := Cell.mkOrdinary (natToBits 0xf4c0 16) #[]

private def opcodeSlice16 (w16 : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (natToBits w16 16) #[])

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (opcodeSlice16 opcode) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectDecodeStepExact (label : String) (opcode : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e => throw (IO.userError s!"{label}: assemble failed {e}")
  | .ok c =>
      if c.bits != natToBits opcode 16 then
        throw (IO.userError s!"{label}: expected {natToBits opcode 16}, got {c.bits}")
      let _ ← expectDecodeStep label (Slice.ofCell c) instr 16

private def dictUGETEXECZGas : Int := computeExactGasBudget instr
private def dictUGETEXECZGasMinusOne : Int := computeExactGasBudgetMinusOne instr

private def gasExact : OracleGasLimits := oracleGasLimitsExact dictUGETEXECZGas
private def gasMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictUGETEXECZGasMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[instr]) : OracleCase :=
  { name := name
    instr := dictUGETEXECZId
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
    instr := dictUGETEXECZId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDICTUGETEXECZFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (tag, rng2) := randNat rng1 0 999_999
  let mkNamed (base : String) (shapeStack : Array Value) (gas : OracleGasLimits := {}) (fuel : Nat := 1_000_000)
      (program : Array Instr := #[instr]) : OracleCase :=
    mkCase (s!"{base}/{tag}") shapeStack gas fuel program
  let case0 : OracleCase :=
    if shape = 0 then
      mkNamed "fuzz/underflow-0" #[]
    else if shape = 1 then
      mkNamed "fuzz/underflow-1" #[.null]
    else if shape = 2 then
      mkNamed "fuzz/underflow-2" #[.null, intV 4]
    else if shape = 3 then
      mkNamed
        "fuzz/err-n-type"
        #[.null, .tuple #[], intV 4]
    else if shape = 4 then
      mkNamed
        "fuzz/err-n-nan"
        #[.cell dictUnsigned4HitRoot, intV 3, .int .nan]
    else if shape = 5 then
      mkNamed "fuzz/err-n-negative" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) (-1))
    else if shape = 6 then
      mkNamed "fuzz/err-n-too-large" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 1024)
    else if shape = 7 then
      mkNamed "fuzz/err-dict-builder" (mkDictCaseStack 3 (.builder Builder.empty) 4)
    else if shape = 8 then
      mkNamed "fuzz/err-dict-tuple" (mkDictCaseStack 3 (.tuple #[]) 4)
    else if shape = 9 then
      mkNamed
        "fuzz/err-key-null"
        (mkDictCaseStack 3 (.cell dictUnsigned4Root) 4 |>.set! 0 (.null))
    else if shape = 10 then
      mkNamed
        "fuzz/err-key-cell"
        (mkDictCaseStack 3 (.cell dictUnsigned4Root) 4 |>.set! 0 (.cell Cell.empty))
    else if shape = 11 then
      mkNamed
        "fuzz/err-key-nan"
        (mkDictCaseStack 3 (.cell dictUnsigned4Root) 4 |>.set! 0 (.int .nan))
    else if shape = 12 then
      mkNamed "fuzz/miss-oob-positive" (mkDictCaseStack 16 (.cell dictUnsigned4Root) 4)
    else if shape = 13 then
      mkNamed "fuzz/miss-oob-negative" (mkDictCaseStack (-1) (.cell dictUnsigned4Root) 4)
    else if shape = 14 then
      mkNamed "fuzz/miss-null-root" (mkDictCaseStack 3 (.null) 4)
    else if shape = 15 then
      mkNamed "fuzz/miss-in-tree" (mkDictCaseStack 2 (.cell dictUnsigned4Root) 4)
    else if shape = 16 then
      mkNamed "fuzz/miss-prefix" (#[(intV 77), intV 16, (.cell dictUnsigned4Root), intV 4])
    else if shape = 17 then
      mkNamed "fuzz/hit" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
    else if shape = 18 then
      mkNamed "fuzz/hit-prefix" (#[(intV 77), intV 3, (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 19 then
      mkNamed "fuzz/boundary-n0-hit" (mkDictCaseStack 0 (.cell dictUnsignedN0Root) 0)
    else if shape = 20 then
      mkNamed "fuzz/boundary-n0-miss" (mkDictCaseStack 1 (.cell dictUnsignedN0Root) 0)
    else if shape = 21 then
      mkNamed
        "fuzz/malformed-root"
        (mkDictCaseStack 3 (.cell malformedDictRoot) 4)
    else if shape = 22 then
      mkNamed
        "fuzz/malformed-root-prefix"
        (#[(intV 77), intV 3, (.cell malformedDictRoot), intV 4])
    else if shape = 23 then
      mkNamed
        "fuzz/gas-exact"
        (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
        gasExact
        1_000_000
        (#[.pushInt (.num dictUGETEXECZGas), .tonEnvOp .setGasLimit, instr])
    else if shape = 24 then
      mkNamed
        "fuzz/gas-exact-minus-one"
        (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
        gasMinusOne
        1_000_000
        (#[.pushInt (.num dictUGETEXECZGasMinusOne), .tonEnvOp .setGasLimit, instr])
    else if shape = 25 then
      mkNamed
        "fuzz/raw-f4bf"
        (#[(intV 3), (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 26 then
      mkNamed
        "fuzz/raw-f4be"
        (#[(intV 3), (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 27 then
      mkNamed
        "fuzz/raw-f4a0"
        (#[(intV 3), (.cell dictUnsigned4HitRoot), intV 4])
    else if shape = 28 then
      mkNamed
        "fuzz/raw-f4c0"
        (#[(intV 3), (.cell dictUnsigned4HitRoot), intV 4])
    else
      mkNamed
        "fuzz/random-hit"
        (#[(intV 9), (.cell dictUnsigned4HitRoot), intV 4])
  ({ case0 with name := case0.name }, rng2)

def suite : InstrSuite where
  id := dictUGETEXECZId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let init : Array Value := mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4
        expectOkStack "unit/dispatch/non-match" (runDictUGETEXECZDispatchFallback .add init) #[intV dispatchSentinel]
        expectOkStack "unit/dispatch/match" (runDictUGETEXECZDispatchFallback instr init) #[] },
    { name := "unit/asm-encoding" -- [B9][B10]
      run := do
        match assembleCp0 [instr] with
        | .ok bits =>
            if bits.bits != natToBits 0xf4bf 16 then
              throw (IO.userError "unit/asm-encoding: expected 0xf4bf")
        | .error e => throw (IO.userError s!"unit/asm-encoding failed: {e}")
        let _ ← expectDecodeStepExact "unit/asm-encoding/decode" 0xf4bf
        expectDecodeInvOpcode "unit/asm-encoding/inv-f4a4" 0xf4a4
        expectDecodeInvOpcode "unit/asm-encoding/inv-f4b0" 0xf4b0
        expectDecodeInvOpcode "unit/asm-encoding/inv-f4c0" 0xf4c0 },
    { name := "unit/errors/underflow" -- [B2]
      run := do
        expectErr "underflow/empty" (runDictUGETEXECZDirect #[]) .stkUnd
        expectErr "underflow/one" (runDictUGETEXECZDirect #[.null]) .stkUnd
        expectErr "underflow/two" (runDictUGETEXECZDirect #[.null, intV 4]) .stkUnd },
    { name := "unit/errors/n-operand" -- [B3]
      run := do
        expectErr "n-not-int" (runDictUGETEXECZDirect #[(intV 3), (.cell dictUnsigned4HitRoot), .tuple #[]]) .typeChk
        expectErr "n-nan" (runDictUGETEXECZDirect #[(intV 3), (.cell dictUnsigned4HitRoot), .int .nan]) .rangeChk
        expectErr "n-negative" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) (-1))) .rangeChk
        expectErr "n-too-large" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 1024)) .rangeChk },
    { name := "unit/errors/dict-key" -- [B4][B5]
      run := do
        expectErr "dict-builder" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.builder Builder.empty) 4)) .typeChk
        expectErr "dict-tuple" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.tuple #[]) 4)) .typeChk
        expectErr "key-null" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.null))) .typeChk
        expectErr "key-cell" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.cell Cell.empty))) .typeChk
        expectErr "key-nan" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.int .nan))) .intOv },
    { name := "unit/exec/miss-paths" -- [B6]
      run := do
        expectOkStack "miss/oob-positive" (runDictUGETEXECZDirect (mkDictCaseStack 16 (.cell dictUnsigned4HitRoot) 4)) #[intV 16]
        expectOkStack "miss/oob-negative" (runDictUGETEXECZDirect (mkDictCaseStack (-1) (.cell dictUnsigned4HitRoot) 4)) #[intV (-1)]
        expectOkStack "miss/null-root" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.null) 4)) #[intV 3]
        expectOkStack
          "miss/prefix-preserved"
          (runDictUGETEXECZDirect (#[(intV 77), intV 16, (.cell dictUnsigned4HitRoot), intV 4]))
          #[intV 77, intV 16] },
    { name := "unit/exec/hit-call" -- [B7]
      run := do
        expectOkStack "hit/no-prefix" (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)) #[]
        expectOkStack "hit/with-prefix" (runDictUGETEXECZDirect (#[(intV 77), intV 3, (.cell dictUnsigned4HitRoot), intV 4])) #[intV 77] },
    { name := "unit/errors/malformed-root" -- [B8]
      run := do
        expectErr
          "malformed-root"
          (runDictUGETEXECZDirect (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
          .dictErr
        let _ ←
          expectRawErr
            "malformed-root/raw"
            (runDictUGETEXECZRaw (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
            .dictErr
        pure () },
    { name := "unit/raw/call-transfer" -- [B7]
      run := do
        let st ←
          expectRawOk
            "raw/call-transfer"
            (runDictUGETEXECZRaw
              (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
              regsWithSentinelC0
              sentinelCc)
        expectCallTransfer "raw/call-transfer" jumpTargetSlice sentinelCc sentinelC0 st }
  ]
  oracle := #[
    -- [B2] underflow and n validation.
    mkCase "oracle/dispatch/non-match" #[], -- [B1]
    mkCase "oracle/dispatch/match" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4), -- [B1]
    mkCase "oracle/underflow/empty" #[], -- [B2]
    mkCase "oracle/underflow/one" #[.null], -- [B2]
    mkCase "oracle/underflow/two" #[.null, (.cell dictUnsigned4HitRoot)], -- [B2]
    mkCase "oracle/n/not-int" (#[intV 3, .cell dictUnsigned4HitRoot, .tuple #[]]), -- [B3]
    mkCase "oracle/n/nan" (#[intV 3, .cell dictUnsigned4HitRoot, .int .nan]), -- [B3]
    mkCase "oracle/n/negative" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) (-1)), -- [B3]
    mkCase "oracle/n/too-large" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 1024), -- [B3]
    -- [B4][B5] dict/key validation.
    mkCase "oracle/dict-builder" (mkDictCaseStack 3 (.builder Builder.empty) 4), -- [B4]
    mkCase "oracle/dict-tuple" (mkDictCaseStack 3 (.tuple #[]) 4), -- [B4]
    mkCase "oracle/key-null" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.null)), -- [B5]
    mkCase "oracle/key-cell" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.cell Cell.empty)), -- [B5]
    mkCase "oracle/key-nan" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4 |>.set! 0 (.int .nan)), -- [B5]
    -- [B6] miss path with pushZ.
    mkCase "oracle/miss/out-of-range-pos" (mkDictCaseStack 16 (.cell dictUnsigned4Root) 4), -- [B6]
    mkCase "oracle/miss/out-of-range-neg" (mkDictCaseStack (-1) (.cell dictUnsigned4Root) 4), -- [B6]
    mkCase "oracle/miss/in-tree-miss" (mkDictCaseStack 2 (.cell dictUnsigned4Root) 4), -- [B6]
    mkCase "oracle/miss/null-root" (mkDictCaseStack 3 (.null) 4), -- [B6]
    mkCase "oracle/miss/prefix-preserved" (#[(intV 77), intV 16, (.cell dictUnsigned4Root), intV 4]), -- [B6]
    mkCase "oracle/boundary/n0-miss" (mkDictCaseStack 1 (.cell dictUnsignedN0Root) 0), -- [B6]
    -- [B7] hit path with call.
    mkCase "oracle/hit/call" (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4), -- [B7]
    mkCase "oracle/hit/call-with-prefix" (#[(intV 77), intV 3, (.cell dictUnsigned4HitRoot), intV 4]), -- [B7]
    -- [B8] malformed root.
    mkCase "oracle/malformed-root" (mkDictCaseStack 3 (.cell malformedDictRoot) 4), -- [B8]
    mkCase "oracle/malformed-root-with-prefix" (#[(intV 99), intV 3, (.cell malformedDictRoot), intV 4]), -- [B8]
    -- [B9][B10] encoding/decoding boundaries.
    mkCaseCode "oracle/raw/f4bf" rawF4bf, -- [B10]
    mkCaseCode "oracle/raw/f4be-variant" rawF4be, -- [B10]
    mkCaseCode "oracle/raw/f4a0-variant" rawF4a0, -- [B10]
    mkCaseCode "oracle/raw/f4a4-invalid" rawF4a4, -- [B10]
    mkCaseCode "oracle/raw/f4b0-invalid" rawF4b0, -- [B10]
    mkCaseCode "oracle/raw/f4c0-invalid" rawF4c0, -- [B10]
    -- [B11] gas accounting.
    mkCase
      "oracle/gas/exact"
      (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
      gasExact
      1_000_000
      (#[.pushInt (.num dictUGETEXECZGas), .tonEnvOp .setGasLimit, instr]),
    mkCase
      "oracle/gas/exact-minus-one"
      (mkDictCaseStack 3 (.cell dictUnsigned4HitRoot) 4)
      gasMinusOne
      1_000_000
      (#[.pushInt (.num dictUGETEXECZGasMinusOne), .tonEnvOp .setGasLimit, instr])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUGETEXECZId
      count := 500
      gen := genDICTUGETEXECZFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETEXECZ
