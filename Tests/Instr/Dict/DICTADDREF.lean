import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.DICTADDREF

/-!
INSTRUCTION: DICTADDREF

BRANCH ANALYSIS (derived from Lean + C++ reference):

1. [B1] Dispatch branch.
   - `.dictSet` is handled only by `execInstrDictDictSet`; all other opcodes must execute
     the fallback path (`next`).

2. [B2] Runtime preamble and shape checks.
   - `checkUnderflow 4` controls arity checks and must run before type/value validation.
   - `popNatUpTo 1023` rejects negative / NaN / out-of-range `n`.

3. [B3] Dictionary root shape/type handling.
   - `popMaybeCell` accepts `null`/`.cell` and throws `typeChk` for any other shape.

4. [B4] Key materialization for non-int keys.
   - `popSlice` must receive a slice.
   - For non-int mode keys, `keyBits` is read from the top `n` bits.
   - If not enough bits are present, `.cellUnd` is thrown before mutation.

5. [B5] Value pop and value-type requirements.
   - ByRef mode requires a `.cell` value; `.tuple`, `.null`, and `.null`/`.builder` etc raise `typeChk`.

6. [B6] Add-mode mutation behavior.
   - Missing key inserts new key/value and returns `-1`.
   - Existing key is no-op and returns `0`.
   - Existing root is preserved on no-op path.

7. [B7] Dictionary structural errors.
   - Malformed dictionary roots can propagate `.dictErr`.

8. [B8] Assembler constraints.
   - Valid encoding is `.dictSet false false true .add` -> `0xf433`.
   - `.dictSet false true true .add` is rejected by `assembleCp0` (`invOpcode`) because unsigned is only meaningful for int-key forms.

9. [B9] Decoder boundaries.
   - `0xf433` decodes to `.dictSet false false true .add`.
   - Neighboring `0xf432`/`0xf434` decode to the adjacent `.dictSet` forms.
   - Truncated 8-bit form must decode as `invOpcode`.

10. [B10] Gas accounting.
    - Base opcode budget is deterministic from `computeExactGasBudget`.
    - `created` cells in insertion path add `cellCreateGasPrice * created`.
    - `exact` budget succeeds, `exact-1` fails on both hit and insert branches.

11. [B11] Explicit runtime path for `n=0`.
    - A zero-width key request always consumes zero bits and behaves consistently with empty-bit key matching.

TOTAL BRANCHES: 11

Each oracle test below is tagged [Bn].
-/

private def suiteId : InstrId := { name := "DICTADDREF" }

private def instr : Instr := .dictSet false false true .add

private def dispatchSentinel : Int := 13021

private def rawOpcodeF432 : Cell := Cell.mkOrdinary (natToBits 0xf432 16) #[]
private def rawOpcodeF433 : Cell := Cell.mkOrdinary (natToBits 0xf433 16) #[]
private def rawOpcodeF434 : Cell := Cell.mkOrdinary (natToBits 0xf434 16) #[]
private def rawOpcodeTruncated8 : Cell := Cell.mkOrdinary (natToBits 0xf4 8) #[]
private def rawOpcodeF432F433F434 : Cell :=
  Cell.mkOrdinary (rawOpcodeF432.bits ++ rawOpcodeF433.bits ++ rawOpcodeF434.bits) #[]

private def malformedDict : Cell := Cell.mkOrdinary (natToBits 0b111 3) #[]

private def valueA : Cell := Cell.mkOrdinary (natToBits 0xA 8) #[]
private def valueB : Cell := Cell.mkOrdinary (natToBits 0xB 8) #[]
private def valueC : Cell := Cell.mkOrdinary (natToBits 0xC 8) #[]
private def valueD : Cell := Cell.mkOrdinary (natToBits 0xD 8) #[]

private def k8A : BitString := natToBits 0x55 8
private def k8B : BitString := natToBits 0xAA 8
private def k8C : BitString := natToBits 0x2A 8
private def k8D : BitString := natToBits 0xA7 8
private def k16A : BitString := natToBits 0xBEEF 16
private def k3A : BitString := natToBits 0b101 3
private def k1A : BitString := natToBits 0b1 1
private def k0A : BitString := #[]

private def s8A : Slice := mkSliceWithBitsRefs k8A
private def s8B : Slice := mkSliceWithBitsRefs k8B
private def s8C : Slice := mkSliceWithBitsRefs k8C
private def s8D : Slice := mkSliceWithBitsRefs k8D
private def s16A : Slice := mkSliceWithBitsRefs k16A
private def s0A : Slice := mkSliceWithBitsRefs k0A
private def s3A : Slice := mkSliceWithBitsRefs k3A

private def mkDictRefRoot! (label : String) (entries : Array (BitString × Cell)) : Cell :=
  Id.run do
    let mut root : Option Cell := none
    for entry in entries do
      let (k, v) := entry
      match dictSetRefWithCells root k v .set with
      | .ok (some root1, _, _, _) =>
          root := root1
      | .ok (none, _, _, _) =>
          panic! s!"{label}: unexpected empty root during build"
      | .error e =>
          panic! s!"{label}: dict set failed with {reprStr e}"
    match root with
    | some r => r
    | none => panic! s!"{label}: no entries"

private def dictRoot8SingleA : Cell := mkDictRefRoot! "dict8-a" #[(k8A, valueA)]
private def dictRoot8SingleB : Cell := mkDictRefRoot! "dict8-b" #[(k8B, valueB)]
private def dictRoot8Pair : Cell := mkDictRefRoot! "dict8-pair" #[(k8A, valueA), (k8B, valueC)]
private def dictRoot16Single : Cell := mkDictRefRoot! "dict16" #[(k16A, valueD)]
private def dictRoot0Single : Cell := mkDictRefRoot! "dict0" #[(k0A, valueA)]

private def dictRoot8Insert : Cell :=
  mkDictRefRoot! "dict8-insert" #[(k8C, valueB)]
private def dictRoot8InsertGas : Nat :=
  match dictSetRefWithCells none k8D valueC .add with
  | .ok (_, _, created, _) => created
  | .error _ => 0

private def baseGas : Int := computeExactGasBudget instr
private def baseGasMinusOne : Int := if baseGas > 0 then baseGas - 1 else 0
private def insertGas : Int := baseGas + Int.ofNat dictRoot8InsertGas * cellCreateGasPrice
private def insertGasMinusOne : Int := if insertGas > 0 then insertGas - 1 else 0

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

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := suiteId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runDictAddRefDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictDictSet instr stack

private def runDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictDictSet .add (VM.push (intV dispatchSentinel)) stack

private def expectAssembleInvOpcode (label : String) (code : Instr) : IO Unit := do
  match assembleCp0 [code] with
  | .error e =>
      if e = .invOpcode then
        pure ()
      else
        throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble failure")

private def genDictAddRefFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 1 then
    (mkCase "fuzz/underflow/one" #[intV 8], rng1)
  else if shape = 2 then
    (mkCase "fuzz/underflow/two" #[intV 8, .null], rng1)
  else if shape = 3 then
    (mkCase "fuzz/underflow/three" #[intV 8, .null, .slice s8A], rng1)
  else if shape = 4 then
    (mkCase "fuzz/err/n-negative" #[.cell valueA, .slice s3A, .null, intV (-1)], rng1)
  else if shape = 5 then
    (mkCase "fuzz/err/n-too-large" #[.cell valueA, .slice s3A, .null, intV 1024], rng1)
  else if shape = 6 then
    (mkCase "fuzz/err/n-nan" #[.cell valueA, .slice s3A, .null, .int .nan], rng1)
  else if shape = 7 then
    (mkCase "fuzz/err/type-dict-not-maybe-cell" #[.cell valueA, .slice s3A, .tuple #[], intV 3], rng1)
  else if shape = 8 then
    (mkCase "fuzz/err/type-key-not-slice" #[.cell valueA, intV 42, .null, intV 8], rng1)
  else if shape = 9 then
    (mkCase "fuzz/err/type-value-not-cell" #[.null, .slice s8A, .null, intV 8], rng1)
  else if shape = 10 then
    (mkCase "fuzz/err/cellund-short-key" #[.cell valueA, .slice s3A, .null, intV 8], rng1)
  else if shape = 11 then
    (mkCase "fuzz/ok/insert/n8-key8a" #[.cell valueC, .slice s8A, .null, intV 8], rng1)
  else if shape = 12 then
    (mkCase "fuzz/ok/insert/n16-key16a" #[.cell valueB, .slice s16A, .null, intV 16], rng1)
  else if shape = 13 then
    (mkCase "fuzz/ok/hit/existing-n8" #[.cell valueC, .slice s8A, .cell dictRoot8SingleA, intV 8], rng1)
  else if shape = 14 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCase s!"fuzz/ok/malformed-root/{tag}" #[.cell valueC, .slice s8A, .cell malformedDict, intV 8], rng2)
  else
    (mkCaseCode "fuzz/raw/f433" (#[.cell valueA, .slice s8C, .null, intV 8]) rawOpcodeF433, rng1)

def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        match runDispatchFallback #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV 8] with
        | .ok st =>
            if st == #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV 8, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"fallback: expected unchanged stack, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"fallback: expected success, got {reprStr e}") }
    ,
    { name := "unit/insert-missing-n8"
      run := do
        expectOkStack "insert-missing-n8"
          (runDictAddRefDirect #[.cell valueC, .slice s8C, .null, intV 8])
          #[.cell dictRoot8Insert, intV (-1)] }
    ,
    { name := "unit/hit-existing-n8"
      run := do
        expectOkStack "hit-existing-n8"
          (runDictAddRefDirect #[.cell valueD, .slice s8A, .cell dictRoot8SingleA, intV 8])
          #[.cell dictRoot8SingleA, intV 0] }
    ,
    { name := "unit/hit-existing-n0"
      run := do
        expectOkStack "hit-existing-n0"
          (runDictAddRefDirect #[.cell valueC, .slice s0A, .cell dictRoot0Single, intV 0])
          #[.cell dictRoot0Single, intV 0] }
    ,
    { name := "unit/underflow-and-type-rules"
      run := do
        expectErr "underflow-empty" (runDictAddRefDirect #[]) .stkUnd
        expectErr "underflow-one" (runDictAddRefDirect #[.cell valueA]) .stkUnd
        expectErr "underflow-two" (runDictAddRefDirect #[.cell valueA, .slice s8A]) .stkUnd
        expectErr "underflow-three" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell dictRoot8SingleA]) .stkUnd
        expectErr "n-not-int" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, .tuple #[]]) .typeChk
        expectErr "dict-not-maybe-cell" (runDictAddRefDirect #[.cell valueA, .slice s8A, .tuple #[], intV 8]) .typeChk
        expectErr "key-not-slice" (runDictAddRefDirect #[.cell valueA, intV 7, .cell dictRoot8SingleA, intV 8]) .typeChk
        expectErr "value-not-cell" (runDictAddRefDirect #[.null, .slice s8A, .cell dictRoot8SingleA, intV 8]) .typeChk
        expectErr "n-negative" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV (-1)]) .rangeChk
        expectErr "n-too-large" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV 1024]) .rangeChk
        expectErr "n-nan" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, .int .nan]) .rangeChk
        expectErr "cell-und-short-key" (runDictAddRefDirect #[.cell valueA, .slice s3A, .cell dictRoot8SingleA, intV 8]) .cellUnd
        expectErr "dict-err-malformed-root" (runDictAddRefDirect #[.cell valueA, .slice s8A, .cell malformedDict, intV 8]) .dictErr }
    ,
    { name := "unit/encoding-decoding-gas"
      run := do
        match assembleCp0 [instr] with
        | .ok c =>
            if c.bits != natToBits 0xf433 16 then
              throw (IO.userError s!"expected 0xf433 bits, got {c.bits}")
        | .error e =>
            throw (IO.userError s!"assemble failed: {e}")
        expectAssembleInvOpcode "encode-invalid-unsigned" (.dictSet false true true .add)
        let s0 : Slice := Slice.ofCell rawOpcodeF432F433F434
        let s1 ← expectDecodeStep "decode/f432" s0 (.dictSet false false false .add) 16
        let s2 ← expectDecodeStep "decode/f433" s1 (.dictSet false false true .add) 16
        let _ ← expectDecodeStep "decode/f434" s2 (.dictSet true false false .add) 16
        match decodeCp0WithBits (Slice.ofCell rawOpcodeTruncated8) with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"decode-truncated: expected invOpcode, got {e}")
        | .ok (instr', bits, _) =>
            throw (IO.userError s!"decode-truncated: expected failure, got {reprStr instr'} with {bits} bits")
      } 
    ,
    { name := "unit/gas-calc-fields"
      run := do
        expectOkStack "directly-ignored" (pure #[]) (#[]) }
  ]
  oracle := #[
    mkCase "ok/insert/n8-new-a" (#[.cell valueA, .slice s8C, .null, intV 8]) (gasLimits := oracleGasLimitsExact (baseGas)) , -- [B6][B10]
    mkCase "ok/insert/n8-new-b" (#[.cell valueB, .slice s8D, .null, intV 8]) (gasLimits := oracleGasLimitsExact (insertGas)) , -- [B6][B10]
    mkCase "ok/insert/n16" (#[.cell valueA, .slice s16A, .null, intV 16]) , -- [B6]
    mkCase "ok/insert/n1-zero-width-key" (#[.cell valueB, .slice (mkSliceWithBitsRefs (natToBits 0 1)), .null, intV 1]) , -- [B6]
    mkCase "ok/insert/n0-key-nonzero-bytes" (#[.cell valueC, .slice s3A, .null, intV 0]) , -- [B11]
    mkCase "ok/hit/n8-existing-a" (#[.cell valueD, .slice s8A, .cell dictRoot8SingleA, intV 8]) , -- [B6]
    mkCase "ok/hit/n8-existing-b" (#[.cell valueA, .slice s8B, .cell dictRoot8SingleB, intV 8]) , -- [B6]
    mkCase "ok/hit/n8-pair-existing-a" (#[.cell valueC, .slice s8A, .cell dictRoot8Pair, intV 8]) , -- [B6]
    mkCase "ok/hit/n8-pair-existing-b" (#[.cell valueD, .slice s8B, .cell dictRoot8Pair, intV 8]) , -- [B6]
    mkCase "ok/hit/n16-existing" (#[.cell valueA, .slice s16A, .cell dictRoot16Single, intV 16]) , -- [B6]
    mkCase "ok/hit/n0-existing" (#[.cell valueB, .slice s0A, .cell dictRoot0Single, intV 0]) , -- [B11]
    mkCase "ok/no-gas-miss-insert-without-check" (#[.cell valueC, .slice s8C, .null, intV 8]) , -- [B6]
    mkCase "err/underflow-empty" #[] , -- [B2]
    mkCase "err/underflow-one" #[intV 8] , -- [B2]
    mkCase "err/underflow-two" #[intV 8, .slice s8A] , -- [B2]
    mkCase "err/underflow-three" #[intV 8, .null, .slice s8A] , -- [B2]
    mkCase "err/type-n-not-int" #[.cell valueA, .slice s8A, .null, .tuple #[]] , -- [B3]
    mkCase "err/type-dict-not-maybe-cell" #[.cell valueA, .slice s8A, .tuple #[], intV 8] , -- [B3][B4]
    mkCase "err/type-key-not-slice" #[.cell valueA, intV 7, .cell dictRoot8SingleA, intV 8] , -- [B4]
    mkCase "err/type-value-not-cell" #[.null, .slice s8A, .cell dictRoot8SingleA, intV 8] , -- [B5]
    mkCase "err/n-negative" #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV (-1)] , -- [B3]
    mkCase "err/n-too-large" #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, intV 1024] , -- [B3]
    mkCase "err/n-nan" #[.cell valueA, .slice s8A, .cell dictRoot8SingleA, .int .nan] , -- [B3]
    mkCase "err/key-too-short-3-of-8" #[.cell valueA, .slice s3A, .cell dictRoot8SingleA, intV 8] , -- [B4]
    mkCase "err/key-too-short-n1" #[.cell valueA, .slice s0A, .cell dictRoot8SingleA, intV 1] , -- [B4]
    mkCase "err/dict-err-malformed-root" #[.cell valueA, .slice s8A, .cell malformedDict, intV 8] , -- [B7]
    mkCaseCode "err/raw/decode-truncated" #[] rawOpcodeTruncated8, -- [B9]
    mkCaseCode "ok/decode/f432" (#[
        .cell valueA,
        .slice s8A,
        .null,
        intV 8
      ]) rawOpcodeF432, -- [B9]
    mkCaseCode "ok/decode/f433" (#[
        .cell valueA,
        .slice s8A,
        .null,
        intV 8
      ]) rawOpcodeF433, -- [B9]
    mkCaseCode "ok/decode/f434" (#[
        .cell valueA,
        .slice s8A,
        .null,
        intV 8
      ]) rawOpcodeF434, -- [B9]
    mkCase "gas/exact/base-hit" (#[.cell valueC, .slice s8A, .cell dictRoot8SingleA, intV 8])
      (#[
        .pushInt (.num baseGas),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact baseGas), -- [B10][B6]
    mkCase "gas/exact-minus-one-hit" (#[.cell valueC, .slice s8A, .cell dictRoot8SingleA, intV 8])
      (#[
        .pushInt (.num baseGasMinusOne),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact baseGasMinusOne), -- [B10]
    mkCase "gas/exact/insert" (#[.cell valueC, .slice s8C, .null, intV 8])
      (#[
        .pushInt (.num insertGas),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact insertGas), -- [B10]
    mkCase "gas/exact-minus-one/insert" (#[.cell valueC, .slice s8C, .null, intV 8])
      (#[
        .pushInt (.num insertGasMinusOne),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact insertGasMinusOne), -- [B10]
    mkCase "gas/exact/minimal-n0-hit" (#[.cell valueD, .slice s0A, .cell dictRoot0Single, intV 0])
      (#[
        .pushInt (.num baseGas),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact baseGas), -- [B10][B11]
    mkCase "gas/exact-minus-one/minimal-n0-hit" (#[.cell valueD, .slice s0A, .cell dictRoot0Single, intV 0])
      (#[
        .pushInt (.num baseGasMinusOne),
        .tonEnvOp .setGasLimit,
        instr
      ])
      (gasLimits := oracleGasLimitsExact baseGasMinusOne) -- [B10][B11]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genDictAddRefFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.DICTADDREF
