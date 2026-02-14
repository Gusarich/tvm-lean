import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.STDICT

/-!
INSTRUCTION: STDICT

BRANCH ANALYSIS (derived from Lean + C++ source):

1. [B1] Dispatch branch.
   - `execInstrDictStdict` executes only `.stdict`; all other opcodes delegate to `next`.

2. [B2] Stack arity gate.
   - `VM.checkUnderflow 2` runs before any stack mutations.
   - With fewer than two operands, `stkUnd` is raised and `popBuilder`/`popMaybeCell` are not attempted.

3. [B3] Operand-order/type behavior.
   - Operand 1 (top of stack) is a builder via `popBuilder`; non-builder top values
     trigger `typeChk` before considering the second argument.
   - Operand 2 is `Dict?` via `popMaybeCell`; non-`cell`/non-`null` values trigger `typeChk`.

4. [B4] `dictRoot` presence branch.
   - `hasRef` is true when the second operand is `.some cell`, false for `.null`.
   - This directly changes required reference capacity and output builder refs.

5. [B5] Capacity gate for write.
   - `canExtendBy 1 needRefs` must hold.
   - Failure condition throws `cellOv` with no output mutation.
   - `needRefs` is `1` for `.some` and `0` for `.null`, so there are bit-capacity-only and
     ref-capacity-sensitive branches in addition to the shared one-bit capacity branch.

6. [B6] Stored payload semantics.
   - On success, one flag bit is appended: `0` for `null`, `1` for non-null.
   - If `hasRef`, that exact root cell is pushed into builder refs as the last ref.

7. [B7] Assembler/decoder behavior.
   - `.stdict` encodes to fixed opcode `0xF400` (16 bits).
   - Decoder path is exact-match for `0xF400`; out-of-family or truncated values must produce `.invOpcode`.

8. [B8] Gas accounting.
   - Base cost is `computeExactGasBudget` for `.stdict` and is constant.
   - There is no additional variable storage/creation penalty inside `execInstrDictStdict`.
   - Therefore exact and exact-minus-one budget checks are the expected gas boundary behavior.

9. [B9] Decoder aliasing/adjacency edge behavior.
   - Adjacent valid instruction `0xF401` decodes as `.skipdict`.
   - `0xF3FF` and truncated `0xF4` are decode-time invalid (`.invOpcode`).

TOTAL BRANCHES: 9

Each oracle test below is tagged [Bn] to the branch(es) it covers.
Any branch not covered by oracle tests MUST be covered by the fuzzer.
-/

private def suiteId : InstrId :=
  { name := "STDICT" }

private def stdictInstr : Instr :=
  .stdict

private def dispatchSentinel : Int :=
  31415

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def rawF3FF : Cell := raw16 0xF3FF
private def rawF400 : Cell := raw16 0xF400
private def rawF401 : Cell := raw16 0xF401
private def rawF4 : Cell := raw16 0xF4

private def sampleCellA : Cell := Cell.mkOrdinary (natToBits 0xA1 8) #[]
private def sampleCellB : Cell := Cell.mkOrdinary (natToBits 0xB2 8) #[]
private def sampleCellC : Cell := Cell.mkOrdinary (natToBits 0xC3 8) #[]
private def sampleCellD : Cell := Cell.mkOrdinary (natToBits 0xD4 8) #[]

private def sampleSlice : Slice :=
  mkSliceFromBits (natToBits 0x5A 8)

private def mkBuilder (bitCount : Nat) (refs : Array Cell := #[]) : Builder :=
  { bits := Array.replicate bitCount false, refs := refs }

private def builderEmpty : Builder :=
  mkBuilder 0

private def builderBits1 : Builder :=
  mkBuilder 1

private def builderBits10 : Builder :=
  mkBuilder 10

private def builderBits1022 : Builder :=
  mkBuilder 1022

private def builderBits1022Refs3 : Builder :=
  mkBuilder 1022 #[sampleCellA, sampleCellB, sampleCellC]

private def builderBits1022Refs0 : Builder :=
  mkBuilder 1022

private def builderBits1023 : Builder :=
  fullBuilder1023

private def builderBits16Refs4 : Builder :=
  mkBuilder 16 #[sampleCellA, sampleCellB, sampleCellC, sampleCellD]

private def storeStdictPayload (b : Builder) (d? : Option Cell) : Builder :=
  let bit : BitString := if d?.isSome then #[true] else #[false]
  let b1 : Builder := b.storeBits bit
  match d? with
  | some c => { b1 with refs := b1.refs.push c }
  | none => b1

private def expectedNoRefFrom (b : Builder) : Builder :=
  storeStdictPayload b none

private def expectedRefFrom (b : Builder) (c : Cell) : Builder :=
  storeStdictPayload b (some c)

private def stdictSetGasExact : Int :=
  computeExactGasBudget stdictInstr

private def stdictSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stdictInstr

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stdictInstr])
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

private def expectDecodeInvOpcode (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error .invOpcode =>
      pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected .invOpcode, got {instr}/{bits}")

private def runSTDICTDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictStdict .add (VM.push (intV dispatchSentinel)) stack

private def runSTDICTDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictStdict stdictInstr stack

private def sampleCellPool : Array Cell :=
  #[sampleCellA, sampleCellB, sampleCellC, sampleCellD]

private def pickSampleCell (rng0 : StdGen) : Cell × StdGen :=
  let (idx, rng1) := randNat rng0 0 (sampleCellPool.size - 1)
  (sampleCellPool[idx]!, rng1)

private def genSTDICTFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 24
  let (cellA, rng2) := pickSampleCell rng1
  let (case0, rng3) :=
    if shape = 0 then
      (mkCase "fuzz/underflow/empty" #[], rng2)
    else if shape = 1 then
      (mkCase "fuzz/underflow/top-only" #[.builder builderEmpty], rng2)
    else if shape = 2 then
      (mkCase "fuzz/underflow/root-only" #[.null], rng2)
    else if shape = 3 then
      (mkCase "fuzz/type/top-not-builder-null" #[.null, .null], rng2)
    else if shape = 4 then
      (mkCase "fuzz/type/top-not-builder-int" #[.builder builderEmpty, intV 7], rng2)
    else if shape = 5 then
      (mkCase "fuzz/type/root-not-cell-or-null" #[.builder builderEmpty, .slice sampleSlice], rng2)
    else if shape = 6 then
      (mkCase "fuzz/type/root-int" #[.builder builderEmpty, intV 42], rng2)
    else if shape = 7 then
      (mkCase "fuzz/ok/no-ref/empty" #[.builder builderEmpty, .null], rng2)
    else if shape = 8 then
      (mkCase "fuzz/ok/no-ref/near-full" #[.builder builderBits1022, .null], rng2)
    else if shape = 9 then
      (mkCase "fuzz/ok/no-ref/with-existing-refs" #[.builder builderBits16Refs4, .null], rng2)
    else if shape = 10 then
      (mkCase "fuzz/ok/ref/empty" #[.builder builderEmpty, .cell cellA], rng2)
    else if shape = 11 then
      (mkCase "fuzz/ok/ref/near-full" #[.builder builderBits1022Refs0, .cell sampleCellA], rng2)
    else if shape = 12 then
      (mkCase "fuzz/ok/ref/existing-refs" #[.builder builderBits1022Refs3, .cell sampleCellB], rng2)
    else if shape = 13 then
      (mkCase "fuzz/ok/deep-stack-preserve" #[.tuple #[], .builder builderBits10, .null], rng2)
    else if shape = 14 then
      (mkCase "fuzz/err/cellov/bits-full-no-ref" #[.builder builderBits1023, .null], rng2)
    else if shape = 15 then
      (mkCase "fuzz/err/cellov/bits-full-ref" #[.builder builderBits1023, .cell sampleCellA], rng2)
    else if shape = 16 then
      (mkCase "fuzz/err/cellov/refs-full" #[.builder builderBits16Refs4, .cell sampleCellB], rng2)
    else if shape = 17 then
      (mkCodeCase "fuzz/raw/stdict" #[.builder builderEmpty, .null] rawF400, rng2)
    else if shape = 18 then
      (mkCodeCase "fuzz/raw/underflow-low" #[] rawF3FF, rng2)
    else if shape = 19 then
      (mkCodeCase "fuzz/raw/truncated-8bit" #[] rawF4, rng2)
    else if shape = 20 then
      (mkCodeCase "fuzz/raw/adjacent-skipdict" #[] rawF401, rng2)
    else if shape = 21 then
      (mkCase
        "fuzz/gas/exact/no-ref"
        #[.builder builderBits1, .null]
        (#[(.pushInt (.num stdictSetGasExact)), .tonEnvOp .setGasLimit, stdictInstr])
        (oracleGasLimitsExact stdictSetGasExact), rng2)
    else if shape = 22 then
      (mkCase
        "fuzz/gas/minus-one/no-ref"
        #[.builder builderBits1, .null]
        (#[(.pushInt (.num stdictSetGasExactMinusOne)), .tonEnvOp .setGasLimit, stdictInstr])
        (oracleGasLimitsExactMinusOne stdictSetGasExactMinusOne), rng2)
    else if shape = 23 then
      (mkCase
        "fuzz/gas/exact/ref"
        #[.builder builderBits1, .cell sampleCellA]
        (#[(.pushInt (.num stdictSetGasExact)), .tonEnvOp .setGasLimit, stdictInstr])
        (oracleGasLimitsExact stdictSetGasExact), rng2)
    else
      (mkCase
        "fuzz/gas/minus-one/ref"
        #[.builder builderBits1, .cell sampleCellB]
        (#[(.pushInt (.num stdictSetGasExactMinusOne)), .tonEnvOp .setGasLimit, stdictInstr])
        (oracleGasLimitsExactMinusOne stdictSetGasExactMinusOne), rng2)
  let (tag, rng4) := randNat rng3 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng4)


def suite : InstrSuite where
  id := suiteId
  unit := #[
    { name := "unit/dispatch/fallback" -- [B1]
      run := do
        match runSTDICTDispatchFallback #[.builder builderEmpty, .null] with
        | .ok st =>
            if st == #[.builder builderEmpty, intV dispatchSentinel] then
              pure ()
            else
              throw (IO.userError s!"dispatch/fallback: expected stack unchanged + sentinel, got {reprStr st}")
        | .error e =>
            throw (IO.userError s!"dispatch/fallback: unexpected error {e}") },
    { name := "unit/runtime/underflow-and-type-order" -- [B2][B3][B4]
      run := do
        expectErr "underflow/empty" (runSTDICTDirect #[]) .stkUnd
        expectErr "underflow/top-builder-only" (runSTDICTDirect #[.builder builderBits10]) .stkUnd
        expectErr "underflow/root-only" (runSTDICTDirect #[.null]) .stkUnd
        expectErr "type/top-not-builder-null"
          (runSTDICTDirect #[.null, .null]) .typeChk
        expectErr "type/top-not-builder-int"
          (runSTDICTDirect #[intV 7, .null]) .typeChk
        expectErr "type/root-not-cell" (runSTDICTDirect #[.builder builderEmpty, intV 7]) .typeChk
        expectErr "type/top-not-builder-slice"
          (runSTDICTDirect #[.slice sampleSlice, .null]) .typeChk },
    { name := "unit/runtime/semantics-branches-no-ref-vs-ref" -- [B4][B5][B6]
      run := do
        expectOkStack "ok/no-ref" (runSTDICTDirect #[.builder builderEmpty, .null])
          #[.builder (expectedNoRefFrom builderEmpty)]
        expectOkStack "ok/no-ref-preserve-refs"
          (runSTDICTDirect #[.builder (mkBuilder 3 #[sampleCellA, sampleCellB]), .null])
          #[.builder (expectedNoRefFrom (mkBuilder 3 #[sampleCellA, sampleCellB]))]
        expectOkStack "ok/ref-adds-one"
          (runSTDICTDirect #[.builder builderBits1, .cell sampleCellA])
          #[.builder (expectedRefFrom builderBits1 sampleCellA)]
        expectOkStack "ok/ref-append-preserve-existing-refs"
          (runSTDICTDirect #[.builder builderBits1022Refs3, .cell sampleCellB])
          #[.builder (expectedRefFrom builderBits1022Refs3 sampleCellB)] },
    { name := "unit/runtime/cell-overflow-branches" -- [B7]
      run := do
        expectErr "cellov/bits-full-no-ref" (runSTDICTDirect #[.builder builderBits1023, .null]) .cellOv
        expectErr "cellov/bits-full-ref" (runSTDICTDirect #[.builder builderBits1023, .cell sampleCellA]) .cellOv
        expectErr "cellov/refs-full" (runSTDICTDirect #[.builder builderBits16Refs4, .cell sampleCellB]) .cellOv
        expectOkStack "ok/bits-full-with-refs-preserved"
          (runSTDICTDirect #[.builder builderBits16Refs4, .null])
          #[.builder (expectedNoRefFrom builderBits16Refs4)] },
    { name := "unit/encoding-and-decoding" -- [B7][B8]
      run := do
        match assembleCp0 [stdictInstr] with
        | .ok code =>
            if code.bits != rawF400.bits then
              throw (IO.userError "assembly produced non-F400 encoding")
        | .error e =>
            throw (IO.userError s!"assembly failed: {e}")
        let stdictSlice : Slice := Slice.ofCell rawF400
        match decodeCp0WithBits stdictSlice with
        | .error e =>
            throw (IO.userError s!"decode failed for F400: {e}")
          | .ok (i, bits, rest) =>
              if i != stdictInstr then
                throw (IO.userError "decode produced wrong instr for F400")
              else
                pure ()
              if bits != 16 then
                throw (IO.userError s!"decode for F400 returned {bits} bits")
              else
                pure ()
              if rest.bitsRemaining + rest.refsRemaining != 0 then
                throw (IO.userError "decode for F400 did not fully consume")
              else
                pure ()
        expectDecodeInvOpcode "decode/underflow-low" rawF3FF
        expectDecodeInvOpcode "decode/truncated" rawF4
        let s2 : Slice := Slice.ofCell rawF401
        match decodeCp0WithBits s2 with
        | .error e => throw (IO.userError s!"decode F401 failed: {e}")
        | .ok (instr, bits, _) =>
            if instr == .skipdict then
              pure ()
            else
              throw (IO.userError "decode F401 expected SKIPDICT")
            if bits = 16 then
              pure ()
            else
              throw (IO.userError s!"decode F401 expected 16 bits, got {bits}") },
    { name := "unit/gas/constant" -- [B8]
      run := do
        if stdictSetGasExact ≤ 0 then
          throw (IO.userError "stdict gas budget should be positive")
        expectOkStack "gas/exact-no-ref"
          (runSTDICTDirect #[.builder builderEmpty, .null])
          #[.builder (expectedNoRefFrom builderEmpty)] }
  ]
  oracle := #[
    mkCase "oracle/underflow/empty" #[] , -- [B2]
    mkCase "oracle/underflow/top-only" #[.builder builderEmpty], -- [B2]
    mkCase "oracle/underflow/root-only" #[.cell sampleCellA], -- [B2]
    mkCase "oracle/type/top-not-builder-null" #[.null, .null], -- [B3]
    mkCase "oracle/type/top-not-builder-int" #[intV 7, .null], -- [B3]
    mkCase "oracle/type/root-not-cell-or-null" #[.builder builderEmpty, .slice sampleSlice], -- [B4]
    mkCase "oracle/type/root-int" #[.builder builderEmpty, intV 1], -- [B4]
    mkCase "oracle/type/root-tuple" #[.builder builderEmpty, .tuple #[]], -- [B4]
    mkCase "oracle/root-null/empty" #[.builder builderEmpty, .null], -- [B5]
    mkCase "oracle/root-null/near-full" #[.builder builderBits1022, .null], -- [B5]
    mkCase "oracle/root-null/full-refs-preserved" #[.builder builderBits16Refs4, .null], -- [B5]
    mkCase "oracle/root-null/full-bits-then-no-ref" #[.builder builderBits1022, .null], -- [B7]
    mkCase "oracle/root-null/with-bit-prefix" #[.builder builderBits10, .null], -- [B6]
    mkCase "oracle/root-cell/empty" #[.builder builderEmpty, .cell sampleCellA], -- [B6]
    mkCase "oracle/root-cell/near-full" #[.builder builderBits1022, .cell sampleCellA], -- [B6]
    mkCase "oracle/root-cell/with-existing-refs" #[.builder builderBits1022Refs3, .cell sampleCellB], -- [B6]
    mkCase "oracle/root-cell/deep-stack-preserve" #[.tuple #[], .builder builderBits10, .cell sampleCellC], -- [B6]
    mkCase "oracle/root-cell/append-preserves-existing-refs" #[.builder builderBits1, .cell sampleCellB], -- [B6]
    mkCase "oracle/root-non-cell-top-only-null-noise" #[.cell sampleCellA, .null], -- [B3]
    mkCase "oracle/root-non-cell-top-builder" #[.slice sampleSlice, .null], -- [B4]
    mkCase "oracle/cellov/near-full-bits-no-ref" #[.builder fullBuilder1023, .null], -- [B7]
    mkCase "oracle/cellov/near-full-bits-ref" #[.builder fullBuilder1023, .cell sampleCellA], -- [B7]
    mkCase "oracle/cellov/refs-full" #[.builder builderBits16Refs4, .cell sampleCellA], -- [B7]
    mkCase "oracle/ok/empty-no-ref" #[.builder builderEmpty, .null], -- [B5]
    mkCase "oracle/ok/bits10-no-ref" #[.builder builderBits10, .null], -- [B5]
    mkCase "oracle/ok/refs3-no-ref" #[.builder (mkBuilder 1 #[sampleCellA, sampleCellB, sampleCellC]), .null], -- [B5]
    mkCase "oracle/ok/empty-ref" #[.builder builderEmpty, .cell sampleCellC], -- [B6]
    mkCase "oracle/ok/bits10-ref" #[.builder builderBits10, .cell sampleCellB], -- [B6]
    mkCase "oracle/ok/refs3-ref-boundary" #[.builder builderBits1022Refs3, .cell sampleCellA], -- [B6]
    mkCodeCase "oracle/raw/f400" #[] rawF400, -- [B7]
    mkCodeCase "oracle/raw/f3ff-inv" #[] rawF3FF, -- [B7]
    mkCodeCase "oracle/raw/truncated" #[] rawF4, -- [B7]
    mkCodeCase "oracle/raw/f401-neighbor" #[] rawF401, -- [B7]
    mkCase "oracle/gas/exact/no-ref" #[.builder builderBits1, .null]
      (#[(.pushInt (.num stdictSetGasExact)), .tonEnvOp .setGasLimit, stdictInstr])
      (oracleGasLimitsExact stdictSetGasExact), -- [B8]
    mkCase "oracle/gas/exact-minus-one/no-ref" #[.builder builderBits1, .null]
      (#[(.pushInt (.num stdictSetGasExactMinusOne)), .tonEnvOp .setGasLimit, stdictInstr])
      (oracleGasLimitsExactMinusOne stdictSetGasExactMinusOne), -- [B8]
    mkCase "oracle/gas/exact/ref" #[.builder builderBits1, .cell sampleCellA]
      (#[(.pushInt (.num stdictSetGasExact)), .tonEnvOp .setGasLimit, stdictInstr])
      (oracleGasLimitsExact stdictSetGasExact), -- [B8]
    mkCase "oracle/gas/exact-minus-one/ref" #[.builder builderBits1, .cell sampleCellA]
      (#[(.pushInt (.num stdictSetGasExactMinusOne)), .tonEnvOp .setGasLimit, stdictInstr])
      (oracleGasLimitsExactMinusOne stdictSetGasExactMinusOne) -- [B8]
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr suiteId
      count := 500
      gen := genSTDICTFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.STDICT
