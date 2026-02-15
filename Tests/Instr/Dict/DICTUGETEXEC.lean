import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTUGETEXEC

/-!
INSTRUCTION: DICTUGETEXEC

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch: only `.dictGetExec true doCall pushZ` executes.
2. [B2] Runtime preconditions: `checkUnderflow 3`, then pop order `n`, `dict`, `idx`.
3. [B3] `n` operand validation via `popNatUpTo 1023`:
   - `.typeChk` for non-int
   - `.rangeChk` for NaN/negative/>1023
4. [B4] `dict` operand validation via `popMaybeCell`:
   - `.null` and `.cell` accepted
   - non-cell non-null values (`.builder`, `.tuple`, ...) -> `.typeChk`
5. [B5] `idx` operand validation:
   - non-int -> `.typeChk`
   - NaN -> `.intOv`
6. [B6] `dictKeyBits?` miss case (range mismatch) does not raise error:
   - `doCall` ignored for stack-result check when miss and `pushZ = false`.
7. [B7] Same miss branch with `pushZ = true` restores original key on stack.
8. [B8] Dictionary hit branch loads continuation and enters transfer path.
9. [B9] `doCall = false` performs jump transfer.
10. [B10] `doCall = true` performs call transfer and updates `c0`.
11. [B11] Malformed dictionary traversal produces `.dictErr`.
12. [B12] Assembler/decoder:
    - valid opcode words: `0xf4bc..0xf4bf`
    - nearby words `0xf4ba`, `0xf4bb`, `0xf4c0` reject.
13. [B13] Gas:
    - fixed base gas only, verify exact-gas success and exact-minus-one failure.

TOTAL BRANCHES: 13

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests is expected to be covered by the fuzzer.
-/

private def dictUGETExecId : InstrId := { name := "DICTUGETEXEC" }

private def mkInstr (doCall pushZ : Bool) : Instr :=
  .dictGetExec true doCall pushZ

private def dispatchSentinel : Int := 12_345

private def methodMarker : Slice := mkSliceFromBits (natToBits 0xC1A5 16)

private def mkDictRootSlice! (label : String) (key : Int) (n : Nat) (value : Slice) : Cell :=
  let keyBits : BitString :=
    match dictKeyBits? key n true with
    | some bits => bits
    | none => panic! s!"{label}: invalid key ({key}, n={n})"
  match dictSetSliceWithCells none keyBits value .set with
  | .ok (some root, _, _, _) => root
  | .ok (none, _, _, _) => panic! s!"{label}: no dict root produced"
  | .error e => panic! s!"{label}: dictSetSliceWithCells failed with {reprStr e}"

private def dictUnsignedHitRoot : Value :=
  .cell (mkDictRootSlice! "dictUnsignedHitRoot" 13 4 methodMarker)

private def dictUnsignedMissRoot : Value :=
  .cell (mkDictRootSlice! "dictUnsignedMissRoot" 7 4 methodMarker)

private def dictUnsignedBoundary0Root : Value :=
  .cell (mkDictRootSlice! "dictUnsignedBoundary0Root" 0 0 methodMarker)

private def malformedDictRoot : Cell := Cell.mkOrdinary (natToBits 1 1) #[]

private def mkDictCaseStack (idx : Int) (dict : Value) (n : Int) : Array Value :=
  #[intV idx, dict, intV n]

private def runDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetExec instr (VM.push (intV dispatchSentinel)) stack

private def runDirect
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetExec instr stack

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

private def expectDecodeInvOpcode (label : String) (opcode : Nat) : IO Unit := do
  match decodeCp0WithBits (mkSliceFromBits (natToBits opcode 16)) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, decode returned {reprStr instr}")
  | .error .invOpcode => pure ()
  | .error e => throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectMethodCont (label : String) (actual : Continuation) : IO Unit := do
  match actual with
  | .ordinary code (.quit 0) _ _ =>
      if code.toCellRemaining != methodMarker.toCellRemaining then
        throw (IO.userError s!"{label}: expected method marker {reprStr methodMarker}, got {reprStr code}")
  | _ => throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr actual}")

private def callReturnFromCc (oldCc : Continuation) (oldC0 : Continuation) : Continuation :=
  match oldCc with
  | .ordinary code _ _ _ =>
      .ordinary code (.quit 0) ({ OrdCregs.empty with c0 := some oldC0 }) { stack := #[], nargs := -1 }
  | _ => .quit 0

private def expectJumpTransfer (label : String) (oldC0 : Continuation) (st : VmState) : IO Unit := do
  expectMethodCont s!"{label}/cc" st.cc
  if st.regs.c0 != oldC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr oldC0}, got {reprStr st.regs.c0}")
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after jump, got {reprStr st.stack}")

private def expectCallTransfer
    (label : String)
    (oldCc : Continuation)
    (oldC0 : Continuation)
    (st : VmState) : IO Unit := do
  expectMethodCont s!"{label}/cc" st.cc
  if !st.stack.isEmpty then
    throw (IO.userError s!"{label}: expected empty stack after call, got {reprStr st.stack}")
  let expectedC0 := callReturnFromCc oldCc oldC0
  if st.regs.c0 != expectedC0 then
    throw (IO.userError s!"{label}: expected c0={reprStr expectedC0}, got {reprStr st.regs.c0}")

private def dictUGETExecExactGas : Int :=
  computeExactGasBudget (mkInstr false false)

private def dictUGETExecExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkInstr false false)

private def oracleGasExact : OracleGasLimits := oracleGasLimitsExact dictUGETExecExactGas
private def oracleGasExactMinusOne : OracleGasLimits := oracleGasLimitsExactMinusOne dictUGETExecExactGasMinusOne

private def mkRawOpcode (opcode : Nat) : Cell :=
  Cell.mkOrdinary (natToBits opcode 16) #[]

private def mkCase
    (name : String)
    (doCall pushZ : Bool)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000)
    (program : Array Instr := #[mkInstr doCall pushZ]) : OracleCase :=
  { name := name
    instr := dictUGETExecId
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
    instr := dictUGETExecId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genDictUGETExecFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 27
  let (doCall, rng2) := randBool rng1
  let (pushZ, rng3) := randBool rng2
  let (tag, rng4) := randNat rng3 0 999_999
  let case0 : OracleCase :=
    match shape with
    | 0 => mkCase "fuzz/underflow/0" doCall pushZ #[]
    | 1 => mkCase "fuzz/underflow/1" doCall pushZ #[.null]
    | 2 => mkCase "fuzz/underflow/2" doCall pushZ #[dictUnsignedHitRoot, intV 13]
    | 3 => mkCase "fuzz/err/n/not-int" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 2 (.tuple #[]))
    | 4 => mkCase "fuzz/err/n/nan" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 2 (.int .nan))
    | 5 => mkCase "fuzz/err/n/negative" false false (mkDictCaseStack 13 dictUnsignedHitRoot (-1))
    | 6 => mkCase "fuzz/err/n/too-large" false false (mkDictCaseStack 13 dictUnsignedHitRoot 1024)
    | 7 => mkCase "fuzz/err/dict-builder" false false (mkDictCaseStack 13 (.builder Builder.empty) 4)
    | 8 => mkCase "fuzz/err/dict-tuple" false false (mkDictCaseStack 13 (.tuple #[]) 4)
    | 9 => mkCase "fuzz/err/key-null" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.null))
    | 10 => mkCase "fuzz/err/key-cell" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.cell Cell.empty))
    | 11 => mkCase "fuzz/err/key-nan" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.int .nan))
    | 12 => mkCase "fuzz/miss/oor-pos" false false (mkDictCaseStack 16 dictUnsignedHitRoot 4)
    | 13 => mkCase "fuzz/miss/oor-neg" false false (mkDictCaseStack (-1) dictUnsignedHitRoot 4)
    | 14 => mkCase "fuzz/miss/oor-pos-z" false true (mkDictCaseStack 16 dictUnsignedHitRoot 4)
    | 15 => mkCase "fuzz/miss/oor-neg-z" false true (mkDictCaseStack (-1) dictUnsignedHitRoot 4)
    | 16 => mkCase "fuzz/miss/null" false false (mkDictCaseStack 16 (.null) 4)
    | 17 => mkCase "fuzz/miss/null-z" false true (mkDictCaseStack 16 (.null) 4)
    | 18 => mkCase "fuzz/miss/in-range" false false (mkDictCaseStack 2 dictUnsignedMissRoot 4)
    | 19 => mkCase "fuzz/miss/in-range-z" false true (mkDictCaseStack 2 dictUnsignedMissRoot 4)
    | 20 => mkCase "fuzz/hit/jump" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4)
    | 21 => mkCase "fuzz/hit/call" true false (mkDictCaseStack 13 dictUnsignedHitRoot 4)
    | 22 => mkCase "fuzz/hit/jump-z" false true (mkDictCaseStack 13 dictUnsignedHitRoot 4)
    | 23 => mkCase "fuzz/hit/call-z" true true (mkDictCaseStack 13 dictUnsignedHitRoot 4)
    | 24 => mkCase "fuzz/malformed-root" false false (mkDictCaseStack 13 (.cell malformedDictRoot) 4)
    | 25 => mkCaseCode "fuzz/raw/f4bb" (mkRawOpcode 0xF4BB) #[]
    | 26 =>
        mkCase
          "fuzz/gas/exact"
          false false
          (mkDictCaseStack 13 dictUnsignedHitRoot 4)
          oracleGasExact
          1_000_000
          (#[.pushInt (.num dictUGETExecExactGas), .tonEnvOp .setGasLimit, mkInstr false false])
    | _ =>
        mkCase
          "fuzz/gas/exact-minus-one"
          false false
          (mkDictCaseStack 13 dictUnsignedHitRoot 4)
          oracleGasExactMinusOne
          1_000_000
          (#[.pushInt (.num dictUGETExecExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false false])
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)


def suite : InstrSuite where
  id := dictUGETExecId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        let st := mkDictCaseStack 13 dictUnsignedHitRoot 4
        expectOkStack "fallback" (runDispatchFallback .add st) (st ++ #[intV dispatchSentinel]) },
    { name := "unit/dispatch/match" -- [B1]
      run := do
        let st := mkDictCaseStack 13 dictUnsignedHitRoot 4
        expectOkStack "match" (runDispatchFallback (mkInstr false false) st) #[] },
    { name := "unit/asm-decode" -- [B12]
      run := do
        match encodeCp0 (mkInstr false false) with
        | .ok bits => let _ ← expectDecodeStep "encode-decode/f4bc" (mkSliceFromBits bits) (mkInstr false false) 16
        | .error e => throw (IO.userError s!"encode-decode/f4bc failed: {e}")
        match encodeCp0 (mkInstr true false) with
        | .ok bits => let _ ← expectDecodeStep "encode-decode/f4bd" (mkSliceFromBits bits) (mkInstr true false) 16
        | .error e => throw (IO.userError s!"encode-decode/f4bd failed: {e}")
        match encodeCp0 (mkInstr false true) with
        | .ok bits => let _ ← expectDecodeStep "encode-decode/f4be" (mkSliceFromBits bits) (mkInstr false true) 16
        | .error e => throw (IO.userError s!"encode-decode/f4be failed: {e}")
        match encodeCp0 (mkInstr true true) with
        | .ok bits => let _ ← expectDecodeStep "encode-decode/f4bf" (mkSliceFromBits bits) (mkInstr true true) 16
        | .error e => throw (IO.userError s!"encode-decode/f4bf failed: {e}")
        let _ ←
          expectDecodeStep "decode/f4bc"
            (mkSliceFromBits (natToBits 0xf4bc 16))
            (.dictGetExec false false true)
            16
        let _ ← expectDecodeStep "decode/f4bd" (mkSliceFromBits (natToBits 0xf4bd 16)) (mkInstr false true) 16
        let _ ←
          expectDecodeStep "decode/f4be"
            (mkSliceFromBits (natToBits 0xf4be 16))
            (.dictGetExec false true true)
            16
        let _ ← expectDecodeStep "decode/f4bf" (mkSliceFromBits (natToBits 0xf4bf 16)) (mkInstr true true) 16
        expectDecodeInvOpcode "decode/f4ba" 0xf4ba
        expectDecodeInvOpcode "decode/f4bb" 0xf4bb
        expectDecodeInvOpcode "decode/f4c0" 0xf4c0 },
    { name := "unit/raw/jump" -- [B9]
      run := do
        let st ←
        expectRawOk
            "raw/jump"
            (runRaw
              (mkInstr false false)
              (mkDictCaseStack 13 dictUnsignedHitRoot 4)
              { Regs.initial with c0 := .quit 17 })
        expectJumpTransfer "raw/jump" (.quit 17) st },
    { name := "unit/raw/call" -- [B10]
      run := do
        let cc := .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty
        let st ←
          expectRawOk
            "raw/call"
            (runRaw
              (mkInstr true false)
              (mkDictCaseStack 13 dictUnsignedHitRoot 4)
              { Regs.initial with c0 := .quit 17 }
              cc)
        expectCallTransfer "raw/call" cc (.quit 17) st }
  ]
  oracle := #[
    mkCase "oracle/dispatch/non-match" false false #[] -- [B1]
    , mkCase "oracle/dispatch/match" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B1]

    mkCase "oracle/underflow/empty" false false #[] , -- [B2]
    mkCase "oracle/underflow/one" false false #[.null], -- [B2]
    mkCase "oracle/underflow/two" false false #[dictUnsignedHitRoot, intV 13], -- [B2]
    mkCase "oracle/n/not-int" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 2 (.tuple #[])), -- [B3]
    mkCase "oracle/n/nan" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 2 (.int .nan)), -- [B3]
    mkCase "oracle/n/negative" false false (mkDictCaseStack 13 dictUnsignedHitRoot (-1)), -- [B3]
    mkCase "oracle/n/too-large" false false (mkDictCaseStack 13 dictUnsignedHitRoot 1024), -- [B3]

    mkCase "oracle/dict/builder" false false (mkDictCaseStack 13 (.builder Builder.empty) 4), -- [B4]
    mkCase "oracle/dict/tuple" false false (mkDictCaseStack 13 (.tuple #[]) 4), -- [B4]

    mkCase "oracle/key/null" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.null)), -- [B5]
    mkCase "oracle/key/cell" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.cell Cell.empty)), -- [B5]
    mkCase "oracle/key/nan" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4 |>.set! 0 (.int .nan)), -- [B5]

    mkCase "oracle/miss/oor-pos" false false (mkDictCaseStack 16 dictUnsignedHitRoot 4), -- [B6]
    mkCase "oracle/miss/oor-neg" false false (mkDictCaseStack (-1) dictUnsignedHitRoot 4), -- [B6]
    mkCase "oracle/miss/in-range" false false (mkDictCaseStack 2 dictUnsignedMissRoot 4), -- [B6]
    mkCase "oracle/miss/prefix" false false (#[intV 77, intV 16, dictUnsignedMissRoot, intV 4]), -- [B6]

    mkCase "oracle/miss/oor-pos-z" false true (mkDictCaseStack 16 dictUnsignedHitRoot 4), -- [B7]
    mkCase "oracle/miss/oor-neg-z" false true (mkDictCaseStack (-1) dictUnsignedHitRoot 4), -- [B7]
    mkCase "oracle/miss/in-range-z" false true (mkDictCaseStack 2 dictUnsignedMissRoot 4), -- [B7]
    mkCase "oracle/miss/prefix-z" false true (#[intV 77, intV 16, dictUnsignedMissRoot, intV 4]), -- [B7]
    mkCase "oracle/miss/null-z" false true (mkDictCaseStack 16 (.null) 4), -- [B7]
    mkCase "oracle/miss/null" false false (mkDictCaseStack 16 (.null) 4), -- [B6]

    mkCase "oracle/hit/jump" false false (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B8][B9]
    mkCase "oracle/hit/call" true false (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B8][B10]
    mkCase "oracle/hit/jump-z" false true (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B8][B9]
    mkCase "oracle/hit/call-z" true true (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B8][B10]
    mkCase "oracle/hit/prefix" false false (#[intV 11, intV 13, dictUnsignedHitRoot, intV 4]), -- [B8][B9]
    mkCase "oracle/hit/prefix-call" true false (#[intV 11, intV 13, dictUnsignedHitRoot, intV 4]), -- [B8][B10]
    mkCase "oracle/hit/boundary-n0" false false (mkDictCaseStack 0 dictUnsignedBoundary0Root 0), -- [B6]

    mkCase "oracle/malformed-root" false false (mkDictCaseStack 13 (.cell malformedDictRoot) 4), -- [B11]

    mkCaseCode "oracle/raw/f4bc" (mkRawOpcode 0xF4BC) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4bd" (mkRawOpcode 0xF4BD) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4be" (mkRawOpcode 0xF4BE) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4bf" (mkRawOpcode 0xF4BF) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4a0" (mkRawOpcode 0xF4A0) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4a1" (mkRawOpcode 0xF4A1) (mkDictCaseStack 13 dictUnsignedHitRoot 4), -- [B12]
    mkCaseCode "oracle/raw/f4ba" (mkRawOpcode 0xF4BA) #[], -- [B12]
    mkCaseCode "oracle/raw/f4bb" (mkRawOpcode 0xF4BB) #[], -- [B12]
    mkCaseCode "oracle/raw/f4c0" (mkRawOpcode 0xF4C0) #[], -- [B12]

    mkCase
      "oracle/gas/exact" -- [B13]
      false false
      (mkDictCaseStack 13 dictUnsignedHitRoot 4)
      oracleGasExact
      1_000_000
      (#[.pushInt (.num dictUGETExecExactGas), .tonEnvOp .setGasLimit, mkInstr false false]),
    mkCase
      "oracle/gas/exact-minus-one" -- [B13]
      false false
      (mkDictCaseStack 13 dictUnsignedHitRoot 4)
      oracleGasExactMinusOne
      1_000_000
      (#[.pushInt (.num dictUGETExecExactGasMinusOne), .tonEnvOp .setGasLimit, mkInstr false false])
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr dictUGETExecId
      count := 500
      gen := genDictUGETExecFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETEXEC
