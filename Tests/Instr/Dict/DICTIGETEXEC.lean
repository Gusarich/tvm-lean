import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIGETEXEC

/-!
INSTRUCTION: DICTIGETEXEC

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [Dispatch] execution handles only `.dictGetExec`; all other instructions fall
   through via `next`.
2. [Runtime preconditions] `checkUnderflow 3`, then pops in this order: `n`, `dict`, `idx`.
3. [n validation] `popNatUpTo 1023` produces `.typeChk` for non-int and
   `.rangeChk` for NaN/negative/>1023.
4. [dict validation] `popMaybeCell` accepts only `null`/`cell`; otherwise `.typeChk`.
5. [key validation] `popIntFinite` gives `.typeChk` for non-int and `.intOv` for NaN.
6. [Key conversion] conversion failure (`dictKeyBits? = none`) does not error; on miss path
   pushes key only if `pushZ`.
7. [Lookup] in-range keys perform `dictLookupWithCells`; `none` result is miss.
8. [Control transfer] `doCall=false` performs jump, `doCall=true` performs call.
9. [Malformed dictionary] traversal/malformed payload is `.dictErr`.
10. [Assembler/decoder] valid words are `0xf4a0..0xf4a3` and
    `0xf4bc..0xf4bf` (mask `0xfffc`); nearby words must reject.
11. [Gas accounting] fixed base gas cost; validate exact success and exact-minus-one failure.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn] to document branch coverage.
Any branch not covered by oracle tests is expected to be covered by the fuzzer.
-/

private def dictIGETExecId : InstrId := { name := "DICTIGETEXEC" }

private def mkInstr (unsigned doCall pushZ : Bool) : Instr :=
  .dictGetExec unsigned doCall pushZ

private def dispatchSentinel : Int := 12_345

private def methodMarker : Slice := mkSliceFromBits (natToBits 0xC1A5 16)

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) (unsigned : Bool) (value : Slice) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n unsigned with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n}, unsigned={unsigned})"
  match dictSetSliceWithCells none keyBits value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! s!"{label}: no dict root produced"
  | .error e => panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def dictSignedHitRoot : Value :=
  .cell (mkDictRootSlice! "dictSignedHitRoot" 3 4 false methodMarker)

private def dictSignedMissRoot : Value :=
  .cell (mkDictRootSlice! "dictSignedMissRoot" 2 4 false methodMarker)

private def dictSignedBoundary0Root : Value :=
  .cell (mkDictRootSlice! "dictSignedBoundary0Root" 0 0 false methodMarker)

private def dictUnsignedHitRoot : Value :=
  .cell (mkDictRootSlice! "dictUnsignedHitRoot" 13 4 true methodMarker)

private def dictUnsignedMissRoot : Value :=
  .cell (mkDictRootSlice! "dictUnsignedMissRoot" 4 4 true methodMarker)

private def dictUnsignedBoundary0Root : Value :=
  .cell (mkDictRootSlice! "dictUnsignedBoundary0Root" 0 0 true methodMarker)

private def mkDictCaseStack (idx : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV idx, dict, intV n]

private def runDictGetExecDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec instr (VM.push (intV dispatchSentinel)) stack

private def runDictGetExecDirect
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def sentinelCc : Continuation :=
  .ordinary (Slice.ofCell (Cell.mkOrdinary (natToBits 0xF00D 16) #[])) (.quit 99) OrdCregs.empty OrdCdata.empty

private def sentinelC0 : Continuation := .quit 17

private def regsWithSentinelC0 : Regs :=
  { Regs.initial with c0 := sentinelC0 }

private def runDictGetExecRaw
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

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode for {opcode}, decode returned {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected invOpcode for {opcode}, got {e}")

private def expectMethodCont (label : String) (actual : Continuation) : IO Unit := do
  match actual with
  | .ordinary code (.quit 0) _ _ =>
      if code.bitsRemaining + code.refsRemaining = 0 then
        throw (IO.userError s!"{label}: expected non-empty continuation code, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr actual}")

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ => .quit 0

private def expectJumpTransfer
    (label : String)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  expectMethodCont (s!"{label}/cc") st.cc
  if st.regs.c0 != oldC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr oldC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after jump, got {reprStr st.stack}")

private def expectCallTransfer
    (label : String)
    (oldCc : Continuation)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  expectMethodCont (s!"{label}/cc") st.cc
  if st.stack.size ≠ 0 then
    throw (IO.userError s!"{label}: expected empty stack after call, got {reprStr st.stack}")
  let expectedC0 := callReturnFromCc oldCc oldC0
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr expectedC0}, got {reprStr st.regs.c0}")

private def dictIGETExecExactGas : Int :=
  computeExactGasBudget (mkInstr false false false)

private def dictIGETExecExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false false false)

private def oracleGasExact : OracleGasLimits := oracleGasLimitsExact dictIGETExecExactGas
private def oracleGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictIGETExecExactGasMinusOne

private def mkRawOpcode (opcode : Nat) : Cell :=
  Cell.mkOrdinary (natToBits opcode 16) #[]

private def mkCase
    (name : String)
    (unsigned doCall pushZ : Bool)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[mkInstr unsigned doCall pushZ]) : OracleCase :=
  { name := name
    instr := dictIGETExecId
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
    instr := dictIGETExecId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDictIGETExecFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (unsigned, rng2) := randBool rng1
  let (doCall, rng3) := randBool rng2
  let (pushZ, rng4) := randBool rng3
  let (tag, rng5) := randNat rng4 0 999_999
  let mkSigned (idx : Int) (root : Value) (n : Int) : OracleCase :=
    mkCase "fuzz/signed" false doCall pushZ (mkDictCaseStack idx root n)
  let mkUnsigned (idx : Int) (root : Value) (n : Int) : OracleCase :=
    mkCase "fuzz/unsigned" true doCall pushZ (mkDictCaseStack idx root n)
  let case0 :=
    if shape = 0 then
      if unsigned then mkUnsigned 13 dictUnsignedHitRoot 4 else mkSigned 3 dictSignedHitRoot 4
    else if shape = 1 then
      if unsigned then mkUnsigned 10 dictUnsignedMissRoot 4 else mkSigned 7 dictSignedMissRoot 4
    else if shape = 2 then
      if unsigned then mkUnsigned 10 dictUnsignedMissRoot 4 else mkSigned 7 dictSignedMissRoot 4
    else if shape = 3 then
      mkCase "fuzz/null-root" unsigned doCall pushZ (mkDictCaseStack (if unsigned then 13 else 7) (.null) 4)
    else if shape = 4 then
      if unsigned then mkUnsigned 16 dictUnsignedHitRoot 4 else mkSigned 8 dictSignedHitRoot 4
    else if shape = 5 then
      if unsigned then mkUnsigned (-1) dictUnsignedHitRoot 4 else mkSigned (-9) dictSignedHitRoot 4
    else if shape = 6 then
      if unsigned then mkUnsigned 16 (.cell malformedDictRoot) 4 else mkSigned 8 (.cell malformedDictRoot) 4
    else if shape = 7 then
      mkCase "fuzz/err-n-not-int" unsigned doCall pushZ (#[
        if unsigned then intV 13 else intV 3,
        if unsigned then dictUnsignedHitRoot else dictSignedHitRoot,
        .tuple #[]
      ])
    else if shape = 8 then
      mkCase "fuzz/err-n-nan" unsigned doCall pushZ (#[
        if unsigned then intV 13 else intV 3,
        if unsigned then dictUnsignedHitRoot else dictSignedHitRoot,
        .int .nan
      ])
    else if shape = 9 then
      mkCase "fuzz/err-n-negative" unsigned doCall pushZ (#[
        if unsigned then intV 13 else intV 3,
        if unsigned then dictUnsignedHitRoot else dictSignedHitRoot,
        intV (-1)
      ])
    else if shape = 10 then
      mkCase "fuzz/err-n-too-large" unsigned doCall pushZ (#[
        if unsigned then intV 13 else intV 3,
        if unsigned then dictUnsignedHitRoot else dictSignedHitRoot,
        intV 1024
      ])
    else if shape = 11 then
      mkCase "fuzz/err-dict-noncell" unsigned doCall pushZ (#[
        if unsigned then intV 13 else intV 3,
        .builder Builder.empty,
        intV 4
      ])
    else if shape = 12 then
      mkCase "fuzz/err-key-null" unsigned doCall pushZ (mkDictCaseStack (if unsigned then 13 else 3) (if unsigned then dictUnsignedHitRoot else dictSignedHitRoot) 4 |>.set! 0 (.null))
    else if shape = 13 then
      mkCase "fuzz/err-key-cell" unsigned doCall pushZ (mkDictCaseStack (if unsigned then 13 else 3) (if unsigned then dictUnsignedHitRoot else dictSignedHitRoot) 4 |>.set! 0 (.cell Cell.empty))
    else if shape = 14 then
      mkCase "fuzz/err-key-nan" unsigned doCall pushZ (mkDictCaseStack (if unsigned then 13 else 3) (if unsigned then dictUnsignedHitRoot else dictSignedHitRoot) 4 |>.set! 0 (.int .nan))
    else if shape = 15 then
      mkCase "fuzz/malformed-root" unsigned doCall pushZ (mkDictCaseStack (if unsigned then 13 else 3) (.cell malformedDictRoot) 4)
    else if shape = 16 then
      mkCase
        "fuzz/gas/exact"
        false false false (mkDictCaseStack 3 (.null) 4)
        (program := #[.pushInt (.num dictIGETExecExactGas), .tonEnvOp .setGasLimit, mkInstr false false false])
        (gasLimits := oracleGasExact)
    else
      mkCase
        "fuzz/gas/exact-minus-one"
        false false false (mkDictCaseStack 3 (.null) 4)
        (program := #[.pushInt (.num dictIGETExecExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false false false])
        (gasLimits := oracleGasExactMinusOne)
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

def suite : InstrSuite where
  id := dictIGETExecId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st := mkDictCaseStack 3 dictSignedHitRoot 4
        expectOkStack
          "dispatch/fallback/non-match"
          (runDictGetExecDispatchFallback .add st)
          #[intV 3, dictSignedHitRoot, intV 4, intV dispatchSentinel]
        expectOkStack
          "dispatch/matched"
          (runDictGetExecDispatchFallback (mkInstr false false false) st)
          #[] },
    { name := "unit/asm-decode" -- [B10]
      run := do
        match encodeCp0 (mkInstr false false false) with
        | .ok bits =>
            if bits != natToBits 0xf4a0 16 then
              throw (IO.userError "unit/asm-decode/f4a0 expected 0xf4a0")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4a0 failed: {e}")
        match encodeCp0 (mkInstr true false false) with
        | .ok bits =>
            if bits != natToBits 0xf4a1 16 then
              throw (IO.userError "unit/asm-decode/f4a1 expected 0xf4a1")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4a1 failed: {e}")
        match encodeCp0 (mkInstr false true false) with
        | .ok bits =>
            if bits != natToBits 0xf4a2 16 then
              throw (IO.userError "unit/asm-decode/f4a2 expected 0xf4a2")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4a2 failed: {e}")
        match encodeCp0 (mkInstr true true false) with
        | .ok bits =>
            if bits != natToBits 0xf4a3 16 then
              throw (IO.userError "unit/asm-decode/f4a3 expected 0xf4a3")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4a3 failed: {e}")
        match encodeCp0 (mkInstr false false true) with
        | .ok bits =>
            if bits != natToBits 0xf4bc 16 then
              throw (IO.userError "unit/asm-decode/f4bc expected 0xf4bc")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4bc failed: {e}")
        match encodeCp0 (mkInstr true false true) with
        | .ok bits =>
            if bits != natToBits 0xf4bd 16 then
              throw (IO.userError "unit/asm-decode/f4bd expected 0xf4bd")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4bd failed: {e}")
        match encodeCp0 (mkInstr false true true) with
        | .ok bits =>
            if bits != natToBits 0xf4be 16 then
              throw (IO.userError "unit/asm-decode/f4be expected 0xf4be")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4be failed: {e}")
        match encodeCp0 (mkInstr true true true) with
        | .ok bits =>
            if bits != natToBits 0xf4bf 16 then
              throw (IO.userError "unit/asm-decode/f4bf expected 0xf4bf")
        | .error e => throw (IO.userError s!"unit/asm-decode/f4bf failed: {e}")
        let _ ← expectDecodeStep "decode/f4a0" (mkSliceFromBits (natToBits 0xf4a0 16)) (mkInstr false false false) 16
        let _ ← expectDecodeStep "decode/f4a1" (mkSliceFromBits (natToBits 0xf4a1 16)) (mkInstr true false false) 16
        let _ ← expectDecodeStep "decode/f4a2" (mkSliceFromBits (natToBits 0xf4a2 16)) (mkInstr false true false) 16
        let _ ← expectDecodeStep "decode/f4a3" (mkSliceFromBits (natToBits 0xf4a3 16)) (mkInstr true true false) 16
        let _ ← expectDecodeStep "decode/f4bc" (mkSliceFromBits (natToBits 0xf4bc 16)) (mkInstr false false true) 16
        let _ ← expectDecodeStep "decode/f4bd" (mkSliceFromBits (natToBits 0xf4bd 16)) (mkInstr true false true) 16
        let _ ← expectDecodeStep "decode/f4be" (mkSliceFromBits (natToBits 0xf4be 16)) (mkInstr false true true) 16
        let _ ← expectDecodeStep "decode/f4bf" (mkSliceFromBits (natToBits 0xf4bf 16)) (mkInstr true true true) 16
        expectDecodeInvOpcode "decode/f4a4" 0xf4a4
        expectDecodeInvOpcode "decode/f4b0" 0xf4b0
        expectDecodeInvOpcode "decode/f4c0" 0xf4c0 },
    { name := "unit/exec/errors/underflow" -- [B2]
      run := do
        expectErr "underflow/empty" (runDictGetExecDirect (mkInstr false false false) #[]) .stkUnd
        expectErr "underflow/one" (runDictGetExecDirect (mkInstr false false false) #[.null]) .stkUnd
        expectErr "underflow/two" (runDictGetExecDirect (mkInstr false false false) #[dictSignedHitRoot, intV 3]) .stkUnd },
    { name := "unit/exec/errors/n-operand" -- [B3]
      run := do
        expectErr "n-not-int" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 2 (.tuple #[]))) .typeChk
        expectErr "n-nan" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 2 (.int .nan))) .rangeChk
        expectErr "n-negative" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot (-1))) .rangeChk
        expectErr "n-too-large" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 1024)) .rangeChk },
    { name := "unit/exec/errors/dict-and-key-type" -- [B4][B5]
      run := do
        expectErr "dict-builder" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 (.builder Builder.empty) 4)) .typeChk
        expectErr "dict-tuple" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 (.tuple #[]) 4)) .typeChk
        expectErr "key-null" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 0 (.null))) .typeChk
        expectErr "key-cell" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 0 (.cell Cell.empty))) .typeChk
        expectErr "key-nan" (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 0 (.int .nan))) .intOv },
    { name := "unit/exec/miss-no-z" -- [B6][B7]
      run := do
        expectOkStack
          "signed-out-of-range"
          (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 8 dictSignedHitRoot 4))
          #[]
        expectOkStack
          "signed-out-of-range-prefix"
          (runDictGetExecDirect (mkInstr false false false) #[intV 77, intV 8, dictSignedHitRoot, intV 4])
          #[intV 77]
        expectOkStack
          "unsigned-out-of-range"
          (runDictGetExecDirect (mkInstr true false false) (mkDictCaseStack 16 dictUnsignedHitRoot 4))
          #[]
        expectOkStack
          "null-root-miss"
          (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 (.null) 4))
          #[]
    },
    { name := "unit/exec/miss-with-pushz" -- [B7]
      run := do
        expectOkStack
          "signed-out-of-range-pushz"
          (runDictGetExecDirect (mkInstr false false true) (mkDictCaseStack 8 dictSignedHitRoot 4))
          #[intV 8]
        expectOkStack
          "signed-out-of-range-pushz-prefix"
          (runDictGetExecDirect (mkInstr false false true) #[intV 77, intV 7, dictSignedMissRoot, intV 4])
          #[intV 77, intV 7]
        expectOkStack
          "unsigned-out-of-range-pushz"
          (runDictGetExecDirect (mkInstr true false true) (mkDictCaseStack 16 dictUnsignedHitRoot 4))
          #[intV 16]
        expectOkStack
          "null-root-pushz"
          (runDictGetExecDirect (mkInstr false false true) (mkDictCaseStack 3 (.null) 4))
          #[intV 3] },
    { name := "unit/exec/hit-paths" -- [B8][B9]
      run := do
        expectOkStack
          "signed-hit-jump"
          (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 dictSignedHitRoot 4))
          #[]
        expectOkStack
          "signed-hit-call"
          (runDictGetExecDirect (mkInstr false true false) (mkDictCaseStack 3 dictSignedHitRoot 4))
          #[]
        expectOkStack
          "unsigned-hit-jump"
          (runDictGetExecDirect (mkInstr true false false) (mkDictCaseStack 13 dictUnsignedHitRoot 4))
          #[]
        expectOkStack
          "unsigned-hit-call"
          (runDictGetExecDirect (mkInstr true true false) (mkDictCaseStack 13 dictUnsignedHitRoot 4))
          #[]
        expectOkStack
          "signed-hit-prefix-preserved"
          (runDictGetExecDirect (mkInstr false false false) #[intV 99, intV 3, dictSignedHitRoot, intV 4])
          #[intV 99] },
    { name := "unit/exec/malformed-root" -- [B9]
      run := do
        expectErrDictLike
          "malformed-signed"
          (runDictGetExecDirect (mkInstr false false false) (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
        expectErrDictLike
          "malformed-unsigned"
          (runDictGetExecDirect (mkInstr true false false) (mkDictCaseStack 13 (.cell malformedDictRoot) 4)) },
    { name := "unit/raw/control-transfer" -- [B8][B9]
      run := do
        let stJump ←
          expectRawOk "raw/jump" (runDictGetExecRaw
            (mkInstr false false false)
            (mkDictCaseStack 3 dictSignedHitRoot 4)
            regsWithSentinelC0
            sentinelCc)
        expectJumpTransfer "raw/jump" sentinelC0 stJump
        let stCall ←
          expectRawOk "raw/call" (runDictGetExecRaw
            (mkInstr false true false)
            (mkDictCaseStack 3 dictSignedHitRoot 4)
            regsWithSentinelC0
            sentinelCc)
        expectCallTransfer "raw/call" sentinelCc sentinelC0 stCall },
    { name := "unit/raw/malformed-root" -- [B9]
      run := do
        let _ ←
          expectRawErrDictLike
            "raw/malformed-root"
            (runDictGetExecRaw (mkInstr false false false) (mkDictCaseStack 3 (.cell malformedDictRoot) 4))
        pure () }
  ]
  oracle := #[
    -- [B1] dispatch.
    mkCase "oracle/dispatch/non-match" false false false #[],
    mkCase "oracle/dispatch/matched" false false false (mkDictCaseStack 3 dictSignedHitRoot 4),
    -- [B2][B3] underflow and n validation.
    mkCase "oracle/underflow/empty" false false false #[],
    mkCase "oracle/underflow/one" false false false #[.null],
    mkCase "oracle/underflow/two" false false false #[dictSignedHitRoot, intV 3],
    mkCase "oracle/n/not-int" false false false (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 2 (.tuple #[])),
    mkCase "oracle/n/nan" false false false (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 2 (.int .nan)),
    mkCase "oracle/n/negative" false false false (mkDictCaseStack 3 dictSignedHitRoot (-1)),
    mkCase "oracle/n/too-large" false false false (mkDictCaseStack 3 dictSignedHitRoot 1024),
    -- [B4] dict argument.
    mkCase "oracle/dict/builder" false false false (mkDictCaseStack 3 (.builder Builder.empty) 4),
    mkCase "oracle/dict/tuple" false false false (mkDictCaseStack 3 (.tuple #[]) 4),
    -- [B5] key validation and conversion.
    mkCase "oracle/key/null" false false false (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 1 (.null)),
    mkCase "oracle/key/cell" false false false (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 1 (.cell Cell.empty)),
    mkCase "oracle/key/nan" false false false (mkDictCaseStack 3 dictSignedHitRoot 4 |>.set! 1 (.int .nan)),
    mkCase "oracle/key/signed-oob-pos" false false false (mkDictCaseStack 8 dictSignedHitRoot 4),
    mkCase "oracle/key/signed-oob-neg" false false false (mkDictCaseStack (-9) dictSignedHitRoot 4),
    mkCase "oracle/key/unsigned-oob-pos" true false false (mkDictCaseStack 16 dictUnsignedHitRoot 4),
    mkCase "oracle/key/unsigned-oob-neg" true false false (mkDictCaseStack (-1) dictUnsignedHitRoot 4),
    -- [B6][B7] miss and pushZ behavior.
    mkCase "oracle/miss/signed" false false false (mkDictCaseStack 7 dictSignedMissRoot 4),
    mkCase "oracle/miss/signed-z" false false true (mkDictCaseStack 7 dictSignedMissRoot 4),
    mkCase "oracle/miss/unsigned" true false false (mkDictCaseStack 10 dictUnsignedMissRoot 4),
    mkCase "oracle/miss/unsigned-z" true false true (mkDictCaseStack 10 dictUnsignedMissRoot 4),
    mkCase "oracle/miss/null" false false false (mkDictCaseStack 3 (.null) 4),
    mkCase "oracle/miss/null-z" false false true (mkDictCaseStack 3 (.null) 4),
    mkCase "oracle/miss/prefix-z" false false true #[intV 77, intV 7, dictSignedMissRoot, intV 4],
    mkCase "oracle/miss/unsigned-prefix-z" true false true #[intV 77, intV 10, dictUnsignedMissRoot, intV 4],
    -- [B8] hit paths and both call/jump variants.
    mkCase "oracle/hit/signed-jump" false false false (mkDictCaseStack 3 dictSignedHitRoot 4),
    mkCase "oracle/hit/signed-call" false true false (mkDictCaseStack 3 dictSignedHitRoot 4),
    mkCase "oracle/hit/unsigned-jump" true false false (mkDictCaseStack 13 dictUnsignedHitRoot 4),
    mkCase "oracle/hit/unsigned-call" true true false (mkDictCaseStack 13 dictUnsignedHitRoot 4),
    mkCase "oracle/hit/signed-jump-z" false false true (mkDictCaseStack 3 dictSignedHitRoot 4),
    mkCase "oracle/hit/signed-call-z" false true true (mkDictCaseStack 3 dictSignedHitRoot 4),
    mkCase "oracle/hit/unsigned-call-z" true true true (mkDictCaseStack 13 dictUnsignedHitRoot 4),
    mkCase "oracle/boundary/signed-0" false false false (mkDictCaseStack 0 dictSignedBoundary0Root 0),
    mkCase "oracle/boundary/unsigned-0" true false false (mkDictCaseStack 0 dictUnsignedBoundary0Root 0),
    -- [B9] malformed root.
    mkCase "oracle/malformed-root/signed" false false false (mkDictCaseStack 3 (.cell malformedDictRoot) 4),
    mkCase "oracle/malformed-root/unsigned" true false false (mkDictCaseStack 13 (.cell malformedDictRoot) 4),
    -- [B10] raw decodes and boundary gaps.
    mkCaseCode "oracle/raw/f4a0" (mkRawOpcode 0xF4A0),
    mkCaseCode "oracle/raw/f4a1" (mkRawOpcode 0xF4A1),
    mkCaseCode "oracle/raw/f4a2" (mkRawOpcode 0xF4A2),
    mkCaseCode "oracle/raw/f4a3" (mkRawOpcode 0xF4A3),
    mkCaseCode "oracle/raw/f4bc" (mkRawOpcode 0xF4BC),
    mkCaseCode "oracle/raw/f4bd" (mkRawOpcode 0xF4BD),
    mkCaseCode "oracle/raw/f4be" (mkRawOpcode 0xF4BE),
    mkCaseCode "oracle/raw/f4bf" (mkRawOpcode 0xF4BF),
    mkCaseCode "oracle/raw/inv-1" (mkRawOpcode 0xF4A4),
    mkCaseCode "oracle/raw/inv-2" (mkRawOpcode 0xF4B0),
    mkCaseCode "oracle/raw/inv-3" (mkRawOpcode 0xF4C0),
    -- [B11] gas.
    mkCase "oracle/gas/exact"
      false false false
      (mkDictCaseStack 3 (.null) 4)
      oracleGasExact
      1_000_000
      (#[.pushInt (.num dictIGETExecExactGas), .tonEnvOp .setGasLimit, mkInstr false false false]),
    mkCase "oracle/gas/exact-minus-one"
      false false false
      (mkDictCaseStack 3 (.null) 4)
      oracleGasExactMinusOne
      1_000_000
      (#[.pushInt (.num dictIGETExecExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false false false])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictIGETExecId
      count := 500
      gen := genDictIGETExecFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIGETEXEC
