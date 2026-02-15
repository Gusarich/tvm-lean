import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTIREMMIN

/-!
INSTRUCTION: DICTIREMMIN

BRANCH ANALYSIS (Lean + C++ reference):

1. [B1] Runtime dispatch path.
   - `.dictGetMinMax` enters `execInstrDictDictGetMinMax`; non-matching instructions
     are delegated to `next`.

2. [B2] Runtime preamble.
   - `VM.checkUnderflow 2` requires a dictionary and `n` on stack.

3. [B3] `n` validation (`VM.popNatUpTo 257`).
   - NaN / negative / >257 is rejected.

4. [B4] Dictionary pop and lookup result.
   - `null` maps to empty dictionary (`none`) and always misses.
   - Lookup miss pushes `(dictRootMaybe, false)` where root in DICTIREMMIN is always pushed.

5. [B5] Hit path with `remove` (`args5 & 16`).
   - `dictDeleteWithCells` is executed and may rebuild dictionary root.
   - New root can become `null` or remain `.cell`.
   - Root replacement contributes `created * cellCreateGasPrice` gas.

6. [B6] Signed key reconstruction.
   - `intKey=true`, `unsigned=false` → `bitsToIntSignedTwos`.

7. [B7] Assembler branch.
   - `ExecInstr.dictGetMinMax 20` must assemble to `0xF494`.
   - In-range-but-gap args (e.g. `24`) must fail with `.invOpcode`.
   - Out-of-range args (`33`) must fail with `.rangeChk`.

8. [B8] Decoder branch.
   - `0xF494` decodes to `.dictGetMinMax 20`.
   - Adjacent family opcodes decode correctly in stream.
   - Gapped opcodes/8-bit truncation fail with `.invOpcode`.

9. [B9] Gas branch.
   - exact budget should pass.
   - exact budget minus one should fail (or raise execution error).
   - remove-with-delete branch consumes extra `cellCreateGasPrice` units.

TOTAL BRANCHES: 9
-/

private def suiteId : InstrId :=
  { name := "DICTIREMMIN" }

private def instr : Instr :=
  .dictGetMinMax 20

private def maxKeyBits (root : Cell) (n : Nat) : Option BitString :=
  match dictMinMaxWithCells (some root) n false true with
  | .ok (some (_, keyBits), _) => some keyBits
  | _ => none

private def dictDeleteCreated (root : Cell) (n : Nat) : Nat :=
  match maxKeyBits root n with
  | some keyBits =>
      match dictDeleteWithCells (some root) keyBits with
      | .ok (_, _, created, _) => created
      | .error _ => 0
  | none => 0

private def mkDictSetRefRoot! (label : String) (n : Nat) (entries : Array (Int × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetRefWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def mkDictSetSliceRoot! (label : String) (n : Nat) (entries : Array (Int × Slice)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      let keyBits :=
        match dictKeyBits? k n false with
        | some b => b
        | none => panic! s!"{label}: invalid key/range ({k}, n={n})"
      match dictSetSliceWithCells root keyBits v .set with
      | .ok (some root1, _ok, _created, _loaded) =>
          root := root1
      | .ok (none, _ok, _created, _loaded) =>
          panic! s!"{label}: unexpected empty root while inserting ({k})"
      | .error e =>
          panic! s!"{label}: dict set failed for ({k}) with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: empty dict construction"

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def badValueSlice : Slice := mkSliceFromBits (natToBits 0xF0 8)

private def dictNull : Value := .null

private def dictSingleRef8 : Cell :=
  mkDictSetRefRoot! "dictSingleRef8" 8 #[(5, valueA)]
private def dictSingleRef8Neg : Cell :=
  mkDictSetRefRoot! "dictSingleRef8Neg" 8 #[( -1, valueA)]
private def dictTwoRef8 : Cell :=
  mkDictSetRefRoot! "dictTwoRef8" 8 #[( -1, valueA), (5, valueB)]
private def dictTwoRef8AfterMin : Cell :=
  mkDictSetRefRoot! "dictTwoRef8AfterMin" 8 #[(5, valueB)]

private def dictThreeRef257 : Cell :=
  mkDictSetRefRoot! "dictThreeRef257" 257 #[(0, valueA), (-1, valueB), (1, valueC)]

private def minInt257 : Int := -(Int.ofNat (1 <<< 256))
private def maxInt257 : Int := Int.ofNat ((1 <<< 256) - 1)
private def dictSingleRef257 : Cell :=
  mkDictSetRefRoot! "dictSingleRef257" 257 #[(0, valueA)]
private def dictSingleRef257Min : Cell :=
  mkDictSetRefRoot! "dictSingleRef257Min" 257 #[(minInt257, valueA)]
private def dictSingleRef257Max : Cell :=
  mkDictSetRefRoot! "dictSingleRef257Max" 257 #[(maxInt257, valueB)]

private def dictSliceSingle8 : Cell :=
  mkDictSetSliceRoot! "dictSliceSingle8" 8 #[(7, badValueSlice)]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0xF 4) #[]

private def twoRef8Created : Nat := dictDeleteCreated dictTwoRef8 8
private def twoRef8Penalty : Int := Int.ofNat twoRef8Created * cellCreateGasPrice
private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := computeExactGasBudgetMinusOne instr
private def removeTwoRef8Gas : Int := baseGas + twoRef8Penalty
private def removeTwoRef8GasMinusOne : Int := if removeTwoRef8Gas > 0 then removeTwoRef8Gas - 1 else 0

private def rawOpcodeF494 : Cell := Cell.mkOrdinary (natToBits 0xF494 16) #[]
private def rawOpcodeF493 : Cell := Cell.mkOrdinary (natToBits 0xF493 16) #[]
private def rawOpcodeF495 : Cell := Cell.mkOrdinary (natToBits 0xF495 16) #[]
private def rawOpcodeF496 : Cell := Cell.mkOrdinary (natToBits 0xF496 16) #[]
private def rawOpcodeF497 : Cell := Cell.mkOrdinary (natToBits 0xF497 16) #[]
private def rawOpcodeF491 : Cell := Cell.mkOrdinary (natToBits 0xF491 16) #[]
private def rawTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xF4 8) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
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

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictGetMinMax .add (VM.push (intV 909)) stack

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictGetMinMax instr stack

private def expectAssembleErr (label : String) (i : Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 [i] with
  | .ok c =>
      throw (IO.userError s!"{label}: expected {expected}, got success {reprStr c.bits}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")

private def expectDecodeErr (label : String) (code : Cell) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok (decoded, bits, _) =>
      throw (IO.userError s!"{label}: expected {expected}, got decode {decoded} consuming {bits}")

def genDictIremMinFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (case0, rng2) :=
    if shape = 0 then
      (mkCase "fuzz/ok/null-n0" (#[dictNull, intV 0]), rng1)
    else if shape = 1 then
      (mkCase "fuzz/ok/null-n8" (#[dictNull, intV 8]), rng1)
    else if shape = 2 then
      (mkCase "fuzz/ok/null-n257" (#[dictNull, intV 257]), rng1)
    else if shape = 3 then
      (mkCase "fuzz/ok/single-ref8" (#[ .cell dictSingleRef8, intV 8]), rng1)
    else if shape = 4 then
      (mkCase "fuzz/ok/single-ref8-alt-n5" (#[ .cell dictSingleRef8, intV 5]), rng1)
    else if shape = 5 then
      (mkCase "fuzz/ok/single-ref8-neg" (#[ .cell dictSingleRef8Neg, intV 8]), rng1)
    else if shape = 6 then
      (mkCase "fuzz/ok/two-ref8" (#[ .cell dictTwoRef8, intV 8]), rng1)
    else if shape = 7 then
      (mkCase "fuzz/ok/three-ref257" (#[ .cell dictThreeRef257, intV 257]), rng1)
    else if shape = 8 then
      (mkCase "fuzz/ok/single-ref257-min" (#[ .cell dictSingleRef257Min, intV 257]), rng1)
    else if shape = 9 then
      (mkCase "fuzz/ok/single-ref257-max" (#[ .cell dictSingleRef257Max, intV 257]), rng1)
    else if shape = 10 then
      (mkCase "fuzz/ok/single-ref8-slice-val" (#[ .cell dictSliceSingle8, intV 8]), rng1)
    else if shape = 11 then
      (mkCase "fuzz/err/underflow-empty" #[], rng1)
    else if shape = 12 then
      (mkCase "fuzz/err/type-top-cell" (#[ .cell valueA, intV 8]), rng1)
    else if shape = 13 then
      (mkCase "fuzz/err/type-top-ref" (#[ .cont (.quit 0), intV 8]), rng1)
    else if shape = 14 then
      (mkCase "fuzz/err/nan" (#[ .cell dictSingleRef8, .int .nan]), rng1)
    else if shape = 15 then
      (mkCase "fuzz/err/n-negative" (#[ .cell dictSingleRef8, intV (-1)]), rng1)
    else if shape = 16 then
      (mkCase "fuzz/err/n-258" (#[ .cell dictSingleRef8, intV 258]), rng1)
    else if shape = 17 then
      (mkCase "fuzz/err/malformed-dict" (#[ .cell malformedDict, intV 8]), rng1)
    else if shape = 18 then
      (mkCase "fuzz/gas/exact" (#[dictNull, intV 0])
        #[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExact baseGas), rng1)
    else if shape = 19 then
      (mkCase "fuzz/gas/exact-minus-one" (#[dictNull, intV 0])
        #[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr]
        (oracleGasLimitsExactMinusOne baseGasMinusOne), rng1)
    else if shape = 20 then
      (mkCase "fuzz/gas/remove-two-ref8"
        (#[ .cell dictTwoRef8, intV 8 ])
        (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExact removeTwoRef8Gas), rng1)
    else if shape = 21 then
      (mkCase "fuzz/gas/remove-two-ref8-oog"
        (#[ .cell dictTwoRef8, intV 8 ])
        (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr]) (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne), rng1)
    else if shape = 22 then
      (mkCodeCase "fuzz/code/f494" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF494, rng1)
    else
      (mkCodeCase "fuzz/code/f497" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF497, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def fuzzSeed : UInt64 := fuzzSeedForInstr suiteId

/--
There are 30+ manually curated oracle entries covering dispatch/runtime/error/decoder/gas branches.
-/
def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        expectOkStack
          "dispatch/fallback"
          (runDispatchFallback #[intV 1, intV 2])
          #[intV 1, intV 2, intV 909] },
    { name := "unit/asm/assemble/exact" -- [B7]
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits = natToBits 0xF494 16 then
              pure ()
            else
              throw (IO.userError s!"expected 0xF494 bits, got {reprStr c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble DICTIREMMIN failed: {reprStr e}") },
    { name := "unit/asm/assemble/gap-reject" -- [B7]
      run := do
        expectAssembleErr "assemble-gap-24" (.dictGetMinMax 24) .invOpcode
        expectAssembleErr "assemble-oob" (.dictGetMinMax 33) .rangeChk },
    { name := "unit/decode/branches" -- [B8]
      run := do
        let s0 := Slice.ofCell
          (Cell.mkOrdinary
            (rawOpcodeF494.bits ++ rawOpcodeF493.bits ++ rawOpcodeF495.bits ++ rawOpcodeF496.bits ++ rawOpcodeF497.bits)
            #[])
        let s1 ← expectDecodeStep "decode/fork" s0 (.dictGetMinMax 20) 16
        let s2 ← expectDecodeStep "decode/prev" s1 (.dictGetMinMax 19) 16
        let s3 ← expectDecodeStep "decode/next" s2 (.dictGetMinMax 21) 16
        let s4 ← expectDecodeStep "decode/nextnext" s3 (.dictGetMinMax 22) 16
        let s5 ← expectDecodeStep "decode/nextnext2" s4 (.dictGetMinMax 23) 16
        if s5.bitsRemaining + s5.refsRemaining != 0 then
          throw (IO.userError "decode did not consume full stream") },
    { name := "unit/decode/invalid-or-truncated" -- [B8]
      run := do
        expectDecodeErr "decode-neighbor-gap" rawOpcodeF491 .invOpcode
        match decodeCp0WithBits (Slice.ofCell rawTruncated8) with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "decode unexpectedly accepted truncated opcode") },
    { name := "unit/exec/empty-null-miss" -- [B4]
      run := do
        expectOkStack "empty-n-8" (runDirect (#[dictNull, intV 8])) #[(.null), intV 0]
        expectOkStack "empty-n-0" (runDirect (#[dictNull, intV 0])) #[(.null), intV 0] },
    { name := "unit/exec/hit-single-min-remove-null" -- [B4][B5][B6]
      run := do
        match runDirect (#[ .cell dictSingleRef8, intV 8]) with
        | .ok #[.null, .slice _, .int (.num 5), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"single-min-n8: expected [null,slice,5,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"single-min-n8: expected success, got {e}") },
    { name := "unit/exec/hit-negative-key-preserves-sign" -- [B6]
      run := do
        match runDirect (#[ .cell dictSingleRef8Neg, intV 8]) with
        | .ok #[.null, .slice _, .int (.num (-1)), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"single-neg-n8: expected [null,slice,-1,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"single-neg-n8: expected success, got {e}") },
    { name := "unit/exec/two-ref-move-root-cell" -- [B5]
      run := do
        match runDirect (#[ .cell dictTwoRef8, intV 8]) with
        | .ok #[.cell _, .slice _, .int (.num (-1)), .int (.num (-1))] =>
            pure ()
        | .ok st =>
            throw (IO.userError s!"two-ref-min-remove-root: expected [cell,slice,-1,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"two-ref-min-remove-root: expected success, got {e}") },
    { name := "unit/exec/257-boundary-min" -- [B6]
      run := do
        match runDirect (#[ .cell dictSingleRef257Min, intV 257]) with
        | .ok #[.null, .slice _, .int (.num k), .int (.num (-1))] =>
            if k = minInt257 then
              pure ()
            else
              throw (IO.userError s!"single-257-min: unexpected key {k}")
        | .ok st =>
            throw (IO.userError s!"single-257-min: expected [null,slice,min,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"single-257-min: expected success, got {e}") },
    { name := "unit/exec/257-boundary-max" -- [B6]
      run := do
        match runDirect (#[ .cell dictSingleRef257Max, intV 257]) with
        | .ok #[.null, .slice _, .int (.num k), .int (.num (-1))] =>
            if k = maxInt257 then
              pure ()
            else
              throw (IO.userError s!"single-257-max: unexpected key {k}")
        | .ok st =>
            throw (IO.userError s!"single-257-max: expected [null,slice,max,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"single-257-max: expected success, got {e}") },
    { name := "unit/exec/marshal-slice-value" -- [B4][B6]
      run := do
        match runDirect (#[ .cell dictSliceSingle8, intV 8]) with
        | .ok #[.null, .slice _, .int (.num 7), .int (.num (-1))] => pure ()
        | .ok st =>
            throw (IO.userError s!"slice-value: expected [null,slice,7,-1], got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"slice-value: expected success, got {e}") },
    { name := "unit/exec/underflow-empty" -- [B2]
      run := do
        expectErr "underflow-empty" (runDirect #[]) .stkUnd
        expectErr "underflow-one" (runDirect #[dictNull]) .stkUnd },
    { name := "unit/exec/n-errs" -- [B3]
      run := do
        expectErr "n-nan" (runDirect (#[dictNull, .int .nan])) .rangeChk
        expectErr "n-negative" (runDirect (#[dictNull, intV (-1)])) .rangeChk
        expectErr "n-too-large" (runDirect (#[dictNull, intV 258])) .rangeChk },
    { name := "unit/exec/type-errors" -- [B4]
      run := do
        match runDirect (#[ .cell valueA, intV 8]) with
        | .error .typeChk => pure ()
        | .error .dictErr => pure ()
        | .error e =>
            throw (IO.userError s!"n-top-not-cell: expected typeChk/dictErr, got {e}")
        | .ok st =>
            throw (IO.userError s!"n-top-not-cell: expected failure, got {reprStr st}")
        expectErr "bad-dict-non-cell" (runDirect (#[ .cont (.quit 0), intV 8])) .typeChk },
    { name := "unit/exec/malformed-dict" -- [B5]
      run := do
        expectErr "bad-dict-cell" (runDirect (#[ .cell malformedDict, intV 8])) .cellUnd
    }
  ]
  oracle := #[
    mkCase "oracle/miss/null/0" (#[dictNull, intV 0]),
    mkCase "oracle/miss/null/8" (#[dictNull, intV 8]),
    mkCase "oracle/miss/null/257" (#[dictNull, intV 257]),
    mkCase "oracle/hit/single8" (#[ .cell dictSingleRef8, intV 8]),
    mkCase "oracle/hit/single8-alt5" (#[ .cell dictSingleRef8, intV 5]),
    mkCase "oracle/hit/single8-negative" (#[ .cell dictSingleRef8Neg, intV 8]),
    mkCase "oracle/hit/two8-min" (#[ .cell dictTwoRef8, intV 8]),
    mkCase "oracle/hit/three257" (#[ .cell dictThreeRef257, intV 257]),
    mkCase "oracle/hit/slice-value" (#[ .cell dictSliceSingle8, intV 8]),
    mkCase "oracle/underflow/empty" (#[]),
    mkCase "oracle/underflow/one" (#[dictNull]),
    mkCase "oracle/err/type-top-int" (#[ .cell valueA, intV 8]),
    mkCase "oracle/err/type-top-cont" (#[ .cont (.quit 0), intV 8]),
    mkCase "oracle/err/nan" (#[ .cell dictSingleRef8, .int .nan]),
    mkCase "oracle/err/n-negative" (#[ .cell dictSingleRef8, intV (-1)]),
    mkCase "oracle/err/n-too-large" (#[ .cell dictSingleRef8, intV 258]),
    mkCase "oracle/err/malformed-dict" (#[ .cell malformedDict, intV 8]),
    mkCase "oracle/gas/exact-miss" (#[dictNull, intV 8]) (#[.pushInt (.num baseGas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact baseGas),
    mkCase "oracle/gas/exact-minus-one-miss" (#[dictNull, intV 8]) (#[.pushInt (.num baseGasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne baseGasMinusOne),
    mkCase "oracle/gas/remove-two-ref8" (#[ .cell dictTwoRef8, intV 8]) (#[.pushInt (.num removeTwoRef8Gas), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExact removeTwoRef8Gas),
    mkCase "oracle/gas/remove-two-ref8-oog" (#[ .cell dictTwoRef8, intV 8]) (#[.pushInt (.num removeTwoRef8GasMinusOne), .tonEnvOp .setGasLimit, instr])
      (oracleGasLimitsExactMinusOne removeTwoRef8GasMinusOne),
    mkCodeCase "oracle/code/f494" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF494,
    mkCodeCase "oracle/code/f493" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF493,
    mkCodeCase "oracle/code/f495" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF495,
    mkCodeCase "oracle/code/f497" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF497,
    mkCodeCase "oracle/decode/truncated8" #[] rawTruncated8,
    mkCodeCase "oracle/code/gap/491" (#[ .cell dictSingleRef8, intV 8 ]) rawOpcodeF491
  ]
  fuzz := #[
    { seed := fuzzSeed
      count := 500
      gen := genDictIremMinFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREMMIN
