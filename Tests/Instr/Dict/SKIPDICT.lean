import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Dict.SKIPDICT

/-!
INSTRUCTION: SKIPDICT

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime dispatch.
   - `execInstrDictSkipdict` matches only `.skipdict`.
   - Any other instruction should forward to `next`.

2. [B2] Runtime arity / stack-underflow.
   - A slice is required.
   - Empty stack fails with `.stkUnd` before any opcode-specific handling.

3. [B3] Runtime operand-type checking.
   - Top-of-stack must be `.slice`.
   - Non-slice values fail with `.typeChk` via `VM.popSlice`.

4. [B4] Bit-length underflow.
   - Instruction requires at least one source bit.
   - If `!s.haveBits 1`, execution fails with `.cellUnd`.

5. [B5] Ref underflow.
   - If leading bit is `1`, `s.haveRefs 1` must hold.
   - When it does not hold, execution fails with `.cellUnd`.

6. [B6] Leading bit = `0` success path.
   - `needRefs := 0`.
   - Output advances bit cursor by 1 and keeps reference cursor unchanged.

7. [B7] Leading bit = `1` success path.
   - `needRefs := 1`.
   - Output advances bit cursor by 1 and reference cursor by 1.

8. [B8] Assembler encoding.
   - `.skipdict` has fixed 16-bit encoding `0xf401`.
   - There are no parameter range branches; no explicit out-of-range rejection applies here.

9. [B9] Decoder behavior.
   - `0xf401` decodes to `.skipdict`.
   - `0xf400`, `0xf402`, 8-bit truncations, and 15-bit truncation must reject with `.invOpcode`.

10. [B10] Gas accounting.
   - Base cost behavior only; no variable dictionary traversal penalty in this opcode path.
   - Explicit exact and exact-minus-one checks still exercise the gas boundary.

TOTAL BRANCHES: 10
Each oracle test below is tagged with the branch(es) it covers.
Any branch not covered by oracle tests is covered by the fuzzer.
-/ 

private def skipDictId : InstrId := { name := "SKIPDICT" }

private def skipDictInstr : Instr := .skipdict

private def skipDictCode : Cell :=
  Cell.mkOrdinary (natToBits 0xf401 16) #[]

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw15 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 15) #[]

private def refA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def refB : Cell :=
  Cell.mkOrdinary (natToBits 0x5b 8) #[]

private def mkSkipSlice (head : Bool) (tail : BitString := #[]) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs ((if head then #[true] else #[false]) ++ tail) refs

private def skip0Empty : Slice :=
  mkSkipSlice false

private def skip0Tail : Slice :=
  mkSkipSlice false (natToBits 0b10101 5)

private def skip0Refs : Slice :=
  mkSkipSlice false (natToBits 0b110 3) #[refA, refB]

private def skip0Deep : Slice :=
  mkSkipSlice false (natToBits 0b11 2)

private def skip1NoRefs : Slice :=
  mkSkipSlice true

private def skip1WithRef : Slice :=
  mkSkipSlice true (natToBits 0b0110 4) #[refA]

private def skip1WithRefs : Slice :=
  mkSkipSlice true (natToBits 0b1011 4) #[refA, refB]

private def skip1Shifted : Slice :=
  (mkSkipSlice false (natToBits 0b111 3) #[refA, refB]).advanceBits 1

private def skip0EmptyOut : Slice :=
  skip0Empty.advanceBits 1

private def skip0TailOut : Slice :=
  skip0Tail.advanceBits 1

private def skip0RefsOut : Slice :=
  skip0Refs.advanceBits 1

private def skip0DeepOut : Slice :=
  skip0Deep.advanceBits 1

private def skip1NoRefsOut : Slice :=
  { skip1NoRefs with bitPos := skip1NoRefs.bitPos + 1, refPos := skip1NoRefs.refPos + 1 }

private def skip1WithRefOut : Slice :=
  { skip1WithRef with bitPos := skip1WithRef.bitPos + 1, refPos := skip1WithRef.refPos + 1 }

private def skip1WithRefsOut : Slice :=
  { skip1WithRefs with bitPos := skip1WithRefs.bitPos + 1, refPos := skip1WithRefs.refPos + 1 }

private def skip1ShiftedOut : Slice :=
  { skip1Shifted with bitPos := skip1Shifted.bitPos + 1, refPos := skip1Shifted.refPos + 1 }

private def dispatchSentinel : Int := 99221

private def runSkipDictDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrDictSkipdict skipDictInstr stack

private def runSkipDictFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrDictSkipdict (.add) (VM.push (intV dispatchSentinel)) stack

private def skipDictGas : Int :=
  computeExactGasBudget skipDictInstr

private def skipDictGasMinusOne : Int :=
  computeExactGasBudgetMinusOne skipDictInstr

private def skipDictGasExact : OracleGasLimits :=
  oracleGasLimitsExact skipDictGas

private def skipDictGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExact skipDictGasMinusOne

private def skipDictProgramExact : Array Instr :=
  #[.pushInt (.num skipDictGas), .tonEnvOp .setGasLimit, skipDictInstr]

private def skipDictProgramExactMinusOne : Array Instr :=
  #[.pushInt (.num skipDictGasMinusOne), .tonEnvOp .setGasLimit, skipDictInstr]

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != 16 then
        throw (IO.userError s!"{label}: expected 16 bits, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected decoded code to consume stream")
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeErr
    (label : String)
    (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      throw (IO.userError s!"{label}: expected invOpcode, got {reprStr instr}")
  | .error e =>
      if e != .invOpcode then
        throw (IO.userError s!"{label}: expected invOpcode, got {e}")

private def expectAssembleOk
    (label : String)
    (instr : Instr)
    (bits : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")
  | .ok cell =>
      if cell.bits.size != 16 || cell.refs.size != 0 || cell.bits != natToBits bits 16 then
        throw (IO.userError s!"{label}: expected exact 16-bit encoding {bits}, got {cell.bits.size} bits")

private def mkCase
    (name : String)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := skipDictId
    codeCell? := some skipDictCode
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
    instr := skipDictId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseProgram
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := skipDictId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def genSKIPDICTFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 39
  let (tag, rng2) := randNat rng1 0 999_999
  let case : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/underflow/empty" #[]
    else if shape = 1 then
      mkCase "fuzz/underflow/one" #[.null]
    else if shape = 2 then
      mkCase "fuzz/type/null" #[.null, intV 7]
    else if shape = 3 then
      mkCase "fuzz/type/int" #[intV 7]
    else if shape = 4 then
      mkCase "fuzz/type/cell" #[.cell refA]
    else if shape = 5 then
      mkCase "fuzz/type/builder" #[.builder Builder.empty]
    else if shape = 6 then
      mkCase "fuzz/type/tuple" #[.tuple #[]]
    else if shape = 7 then
      mkCase "fuzz/underflow/bits" #[.slice (mkSliceFromBits #[])]
    else if shape = 8 then
      mkCase "fuzz/underflow/bits/deep" #[.null, .slice (mkSliceFromBits #[])]
    else if shape = 9 then
      mkCase "fuzz/ref-underflow/no-refs" #[.slice skip1NoRefs]
    else if shape = 10 then
      mkCase "fuzz/ref-underflow/deep" #[intV 11, .slice skip1NoRefs]
    else if shape = 11 then
      mkCase "fuzz/ok/bit0-empty" #[.slice skip0Empty]
    else if shape = 12 then
      mkCase "fuzz/ok/bit0-tail" #[.slice skip0Tail]
    else if shape = 13 then
      mkCase "fuzz/ok/bit0-refs" #[.slice skip0Refs]
    else if shape = 14 then
      mkCase "fuzz/ok/bit0-deep" #[.slice skip0Deep, intV 9]
    else if shape = 15 then
      mkCase "fuzz/ok/bit1-with-ref" #[.slice skip1WithRef]
    else if shape = 16 then
      mkCase "fuzz/ok/bit1-two-refs" #[.slice skip1WithRefs]
    else if shape = 17 then
      mkCase "fuzz/ok/bit1-shifted" #[.slice skip1Shifted]
    else if shape = 18 then
      mkCaseCode "fuzz/asm/roundtrip" #[.slice skip0Empty] skipDictCode
    else if shape = 19 then
      mkCaseCode "fuzz/decode/target" #[] skipDictCode
    else if shape = 20 then
      mkCaseCode "fuzz/decode/lower" #[] (raw16 0xf400)
    else if shape = 21 then
      mkCaseCode "fuzz/decode/upper" #[] (raw16 0xf402)
    else if shape = 22 then
      mkCaseCode "fuzz/decode/trunc8" #[] (raw8 0xf4)
    else if shape = 23 then
      mkCaseCode "fuzz/decode/trunc15" #[] (raw15 (0xf401 >>> 1))
    else if shape = 24 then
      mkCaseProgram "fuzz/gas/exact" #[.slice skip0Tail] skipDictProgramExact (gasLimits := skipDictGasExact)
    else if shape = 25 then
      mkCaseProgram "fuzz/gas/exact-minus-one" #[.slice skip1WithRef] skipDictProgramExactMinusOne (gasLimits := skipDictGasExactMinusOne)
    else if shape = 26 then
      mkCase "fuzz/ok/bit0-deep-stack" #[intV 7, .slice skip0Tail, .cell refA]
    else if shape = 27 then
      mkCase "fuzz/ok/bit1-deep-stack" #[.null, intV 9, .slice skip1WithRefs]
    else if shape = 28 then
      mkCase "fuzz/ok/bit1-tail-two-refs" #[.tuple #[], .slice skip1WithRefs]
    else if shape = 29 then
      mkCase "fuzz/type/null-deep" #[.cell refA, .null]
    else if shape = 30 then
      mkCase "fuzz/gas/exact-same" #[.slice skip0Empty] skipDictGasExact
    else if shape = 31 then
      mkCase "fuzz/gas/exact-minus-one-same" #[.slice skip1WithRef] skipDictGasExactMinusOne
    else if shape = 32 then
      mkCase "fuzz/redundancy" #[.slice skip0Refs] 
    else
      mkCase "fuzz/ref-underflow-noise" #[.slice skip1WithRefs]
  ({ name := s!"{case.name}/{tag}", instr := case.instr, codeCell? := case.codeCell?, program := case.program,
     initStack := case.initStack, initCregs := case.initCregs, initC7 := case.initC7, initLibraries := case.initLibraries,
     gasLimits := case.gasLimits, fuel := case.fuel }, rng2)


def suite : InstrSuite where
  id := skipDictId
  unit := #[
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "fallback/empty" (runSkipDictFallback #[]) #[intV dispatchSentinel]
        expectOkStack "fallback/deep" (runSkipDictFallback #[.null, .slice skip0Tail, intV 11])
          #[.null, .slice skip0Tail, intV 11, intV dispatchSentinel]
    },
    { name := "unit/runtime/underflow"
      run := do
        expectErr "underflow/empty" (runSkipDictDirect #[]) .stkUnd
    },
    { name := "unit/runtime/type"
      run := do
        expectErr "type/top-null" (runSkipDictDirect #[.null]) .typeChk
        expectErr "type/top-int" (runSkipDictDirect #[intV 7]) .typeChk
        expectErr "type/top-cell" (runSkipDictDirect #[.cell refA]) .typeChk
        expectErr "type/top-builder" (runSkipDictDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runSkipDictDirect #[.tuple #[]]) .typeChk
    },
    { name := "unit/runtime/bit-underflow"
      run := do
        expectErr "bit-underflow/empty" (runSkipDictDirect #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "bit-underflow/empty-deep" (runSkipDictDirect #[.cell refB, .slice (mkSliceFromBits #[])]) .cellUnd
    },
    { name := "unit/runtime/ref-underflow"
      run := do
        expectErr "ref-underflow/no-ref" (runSkipDictDirect #[.slice skip1NoRefs]) .cellUnd
        expectErr "ref-underflow/no-ref-deep" (runSkipDictDirect #[.null, .slice skip1NoRefs]) .cellUnd
    },
    { name := "unit/runtime/bit0-path"
      run := do
        expectOkStack "bit0/no-tail" (runSkipDictDirect #[.slice skip0Empty]) #[.slice skip0EmptyOut]
        expectOkStack "bit0/tail" (runSkipDictDirect #[.slice skip0Tail]) #[.slice skip0TailOut]
        expectOkStack "bit0/refs" (runSkipDictDirect #[.slice skip0Refs]) #[.slice skip0RefsOut]
        expectOkStack "bit0/deep" (runSkipDictDirect #[.cell refA, .slice skip0Deep]) #[.cell refA, .slice skip0DeepOut]
    },
    { name := "unit/runtime/bit1-path"
      run := do
        expectOkStack "bit1/with-ref" (runSkipDictDirect #[.slice skip1WithRef]) #[.slice skip1WithRefOut]
        expectOkStack "bit1/two-refs" (runSkipDictDirect #[.slice skip1WithRefs]) #[.slice skip1WithRefsOut]
        expectOkStack "bit1/shifted" (runSkipDictDirect #[.slice skip1Shifted]) #[.slice skip1ShiftedOut]
        expectOkStack "bit1/deep" (runSkipDictDirect #[.tuple #[], .slice skip1WithRef]) #[.tuple #[], .slice skip1WithRefOut]
    },
    { name := "unit/asmdecode/decode"
      run := do
        expectDecodeOk "decode/target" skipDictCode skipDictInstr
        expectDecodeErr "decode/lower-neighbor" (raw16 0xf400)
        expectDecodeErr "decode/upper-neighbor" (raw16 0xf402)
        expectDecodeErr "decode/trunc8" (raw8 0xf4)
        expectDecodeErr "decode/trunc15" (raw15 (0xf401 >>> 1))
    },
    { name := "unit/asmdecode/assemble"
      run := do
        expectAssembleOk "assemble/skipdict" skipDictInstr 0xf401
    }
  ]
  oracle := #[
    -- [B1][B6]
    mkCase "oracle/bit0/no-tail" #[.slice skip0Empty],
    -- [B1][B6]
    mkCase "oracle/bit0/tail" #[.slice skip0Tail],
    -- [B1][B6]
    mkCase "oracle/bit0/refs" #[.slice skip0Refs],
    -- [B1][B6]
    mkCase "oracle/bit0/deep" #[.cell refA, .slice skip0Deep],
    -- [B1][B7]
    mkCase "oracle/bit1/with-ref" #[.slice skip1WithRef],
    -- [B1][B7]
    mkCase "oracle/bit1/two-refs" #[.slice skip1WithRefs],
    -- [B1][B7]
    mkCase "oracle/bit1/shifted" #[.slice skip1Shifted],
    -- [B1][B7]
    mkCase "oracle/bit1/deep" #[.null, .slice skip1WithRef],

    -- [B2]
    mkCase "oracle/underflow/empty" #[],
    -- [B2]
    mkCase "oracle/underflow/one" #[.null],

    -- [B3]
    mkCase "oracle/type/null" #[.null, intV 11],
    -- [B3]
    mkCase "oracle/type/int" #[intV 11],
    -- [B3]
    mkCase "oracle/type/cell" #[.cell refA],
    -- [B3]
    mkCase "oracle/type/builder" #[.builder Builder.empty],
    -- [B3]
    mkCase "oracle/type/tuple" #[.tuple #[]],

    -- [B4]
    mkCase "oracle/err/bit-underflow" #[.slice (mkSliceFromBits #[])],
    -- [B4]
    mkCase "oracle/err/bit-underflow-deep" #[.cell refA, .slice (mkSliceFromBits #[])],

    -- [B5]
    mkCase "oracle/err/ref-underflow/no-ref" #[.slice skip1NoRefs],
    -- [B5]
    mkCase "oracle/err/ref-underflow-deep" #[.cell refA, .slice skip1NoRefs],

    -- [B8]
    mkCaseCode "oracle/asm/roundtrip" #[.slice skip0Empty] skipDictCode,

    -- [B9]
    mkCaseCode "oracle/decode/target" #[] skipDictCode,
    -- [B9]
    mkCaseCode "oracle/decode/lower" #[] (raw16 0xf400),
    -- [B9]
    mkCaseCode "oracle/decode/upper" #[] (raw16 0xf402),
    -- [B9]
    mkCaseCode "oracle/decode/trunc8" #[] (raw8 0xf4),
    -- [B9]
    mkCaseCode "oracle/decode/trunc15" #[] (raw15 (0xf401 >>> 1)),

    -- [B10]
    mkCaseProgram "oracle/gas/exact" #[.slice skip0Empty] skipDictProgramExact (gasLimits := skipDictGasExact),
    -- [B10]
    mkCaseProgram "oracle/gas/exact-minus-one" #[.slice skip1WithRef] skipDictProgramExactMinusOne (gasLimits := skipDictGasExactMinusOne),
    -- [B10]
    mkCase "oracle/gas/hit-extra-stack" #[.cell refA, .slice skip0Tail] (gasLimits := skipDictGasExact),
    -- [B10]
    mkCase "oracle/gas/minus-one-extra-stack" #[.cell refB, .slice skip1WithRef] (gasLimits := skipDictGasExactMinusOne)
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr skipDictId
      count := 500
      gen := genSKIPDICTFuzzCase
    }
  ]

initialize registerSuite suite

end Tests.Instr.Dict.SKIPDICT
