import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STVARINT32

/-
STVARINT32 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stVarInt true 32)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STVARINT32` encode: `0xfa07`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa07` decode to `.stVarInt true 32`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_var_integer`, `util::store_var_integer` with `len_bits=5`, `sgnd=true`).

Branch map used for this suite:
- Lean STVARINT32 path: 12 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; kind guard; x pop/type; NaN split; builder pop/type;
   signed lenBytes derivation; len overflow guard; capacity guard; payload store path).
- C++ STVARINT32 path: 9 branch sites / 13 aligned outcomes
  (`check_underflow(2)`; x then builder pop; len range before capacity; success push).

Key risk areas:
- stack order is `... builder x` (`x` on top);
- len overflow (`lenBytes >= 32`) must throw `rangeChk` before capacity checks;
- `NaN` throws `rangeChk` before builder pop;
- exact 31-byte signed boundary must pass; 32-byte requirement must fail.
-/

private def stvarint32Id : InstrId := { name := "STVARINT32" }

private def stvarint32Instr : Instr :=
  .cellExt (.stVarInt true 32)

private def mkStvarint32Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stvarint32Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvarint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStvarint32ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvarint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStvarint32Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stvarint32Instr stack

private def runStvarint32DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStvarint32DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 425)) stack

private def maxSigned31Bytes : Int := intPow2 247 - 1

private def minSigned31Bytes : Int := -(intPow2 247)

private def overflowPosSigned31Bytes : Int := intPow2 247

private def overflowNegSigned31Bytes : Int := -(intPow2 247) - 1

private def samplePos : Int := intPow2 200 + 12345

private def sampleNeg : Int := -(intPow2 200) - 12345

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def fullBuilderProgramWith (x : IntVal) : Array Instr :=
  build1023Program ++ #[.pushInt x, stvarint32Instr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stvarint32Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-2)), stvarint32Instr
  ]

private def stvarint32SetGasExact : Int :=
  computeExactGasBudget stvarint32Instr

private def stvarint32SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stvarint32Instr

private def encodeSignedVarIntBits (lenBits : Nat) (n : Int) : Except Excno BitString := do
  let lenBytes : Nat := (intSignedBitSizeTwos n + 7) / 8
  let payload ← intToBitsTwos n (lenBytes * 8)
  pure (natToBits lenBytes lenBits ++ payload)

private def pickStvarint32InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then maxSigned31Bytes
    else if pick = 4 then minSigned31Bytes
    else if pick = 5 then samplePos
    else if pick = 6 then sampleNeg
    else 42
  (x, rng')

private def genStvarint32FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  if shape = 0 then
    let (x, rng2) := pickStvarint32InRange rng1
    (mkStvarint32Case s!"fuzz/ok/top-only/x-{x}" #[.builder Builder.empty, intV x], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStvarint32InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 107 else .cell Cell.empty
    (mkStvarint32Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, .builder Builder.empty, intV x], rng3)
  else if shape = 2 then
    (mkStvarint32Case "fuzz/range/overflow-pos" #[.builder Builder.empty, intV overflowPosSigned31Bytes], rng1)
  else if shape = 3 then
    (mkStvarint32Case "fuzz/range/overflow-neg" #[.builder Builder.empty, intV overflowNegSigned31Bytes], rng1)
  else if shape = 4 then
    (mkStvarint32Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStvarint32Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStvarint32Case "fuzz/type/x-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 7 then
    (mkStvarint32Case "fuzz/type/builder-not-builder" #[intV 2, intV 1], rng1)
  else if shape = 8 then
    (mkStvarint32ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 9 then
    let (x, rng2) := pickStvarint32InRange rng1
    (mkStvarint32ProgramCase s!"fuzz/cellov/in-range-x-{x}" #[] (fullBuilderProgramWith (.num x)), rng2)
  else
    (mkStvarint32ProgramCase "fuzz/range-before-cellov-overflow" #[]
      (fullBuilderProgramWith (.num overflowPosSigned31Bytes)), rng1)

def suite : InstrSuite where
  id := stvarint32Id
  unit := #[
    { name := "unit/direct/success-boundaries-and-encoding"
      run := do
        let checks : Array Int := #[0, 1, -1, 127, -128, samplePos, sampleNeg, maxSigned31Bytes, minSigned31Bytes]
        for x in checks do
          let bs ←
            match encodeSignedVarIntBits 5 x with
            | .ok out => pure out
            | .error e => throw (IO.userError s!"unexpected encode error {e} for x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/x-{x}"
            (runStvarint32Direct #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let bs ←
          match encodeSignedVarIntBits 5 (-2) with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let appended := prefBuilder.storeBits bs
        expectOkStack "ok/append-existing-bits"
          (runStvarint32Direct #[.builder prefBuilder, intV (-2)])
          #[.builder appended]

        let deepBits ←
          match encodeSignedVarIntBits 5 7 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let expectedDeep := Builder.empty.storeBits deepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStvarint32Direct #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-and-order"
      run := do
        -- Branch map: signed len overflow branch (`lenBytes >= 32`) -> `rangeChk`.
        expectErr "range/overflow-pos"
          (runStvarint32Direct #[.builder Builder.empty, intV overflowPosSigned31Bytes]) .rangeChk
        expectErr "range/overflow-neg"
          (runStvarint32Direct #[.builder Builder.empty, intV overflowNegSigned31Bytes]) .rangeChk
        expectErr "range/nan"
          (runStvarint32Direct #[.builder Builder.empty, .int .nan]) .rangeChk

        -- Branch map: `NaN` rejection happens before builder pop/type/capacity branches.
        expectErr "error-order/range-nan-before-builder-type"
          (runStvarint32Direct #[.null, .int .nan]) .rangeChk
        expectErr "error-order/range-before-cellov-overflow"
          (runStvarint32Direct #[.builder fullBuilder1023, intV overflowPosSigned31Bytes]) .rangeChk
        expectErr "error-order/range-before-cellov-nan"
          (runStvarint32Direct #[.builder fullBuilder1023, .int .nan]) .rangeChk

        expectErr "invopcode/invalid-kind-24"
          (runStvarint32DirectInstr (.cellExt (.stVarInt true 24)) #[.builder Builder.empty, intV 0]) .invOpcode }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        -- Branch map: `checkUnderflow 2` short-circuits before any type pops.
        expectErr "underflow/empty" (runStvarint32Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStvarint32Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-int-only" (runStvarint32Direct #[intV 7]) .stkUnd
        expectErr "underflow/single-non-int" (runStvarint32Direct #[.null]) .stkUnd

        expectErr "type/x-pop-first-top-not-int"
          (runStvarint32Direct #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/x-pop-first-top-builder"
          (runStvarint32Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/builder-pop-second"
          (runStvarint32Direct #[intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-in-range-path"
      run := do
        -- Branch map: in-range values reach capacity guard (`canExtendBy`) -> `cellOv` on full builder.
        expectErr "cellov/full-builder-x0"
          (runStvarint32Direct #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "cellov/full-builder-xneg1"
          (runStvarint32Direct #[.builder fullBuilder1023, intV (-1)]) .cellOv
        expectErr "cellov/full-builder-xmax31"
          (runStvarint32Direct #[.builder fullBuilder1023, intV maxSigned31Bytes]) .cellOv
        expectErr "cellov/full-builder-xsample"
          (runStvarint32Direct #[.builder fullBuilder1023, intV samplePos]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stvarint32Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stvarint32" s0 stvarint32Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stVarInt true 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvarint32/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvarint32/kind24: expected assemble invOpcode, got success")
        match assembleCp0 [.cellExt (.stVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvarint32/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvarint32/uint16-alias: expected assemble invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStvarint32DispatchFallback #[.null])
          #[.null, intV 425] }
  ]
  oracle := #[
    -- Branch map: success path (len derivation + payload store) for representative signed values.
    mkStvarint32Case "ok/zero" #[.builder Builder.empty, intV 0],
    mkStvarint32Case "ok/one" #[.builder Builder.empty, intV 1],
    mkStvarint32Case "ok/neg-one" #[.builder Builder.empty, intV (-1)],
    mkStvarint32Case "ok/127" #[.builder Builder.empty, intV 127],
    mkStvarint32Case "ok/minus-128" #[.builder Builder.empty, intV (-128)],
    mkStvarint32Case "ok/sample-pos" #[.builder Builder.empty, intV samplePos],
    mkStvarint32Case "ok/sample-neg" #[.builder Builder.empty, intV sampleNeg],
    mkStvarint32Case "ok/max-signed-31-bytes" #[.builder Builder.empty, intV maxSigned31Bytes],
    mkStvarint32Case "ok/min-signed-31-bytes" #[.builder Builder.empty, intV minSigned31Bytes],
    mkStvarint32Case "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7],
    mkStvarint32ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    -- Branch map: range checks, including NaN-before-builder-type ordering.
    mkStvarint32Case "range/overflow-pos" #[.builder Builder.empty, intV overflowPosSigned31Bytes],
    mkStvarint32Case "range/overflow-neg" #[.builder Builder.empty, intV overflowNegSigned31Bytes],
    mkStvarint32ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStvarint32ProgramCase "range/nan-before-builder-type" #[.null] rangeNanProgram,
    mkStvarint32ProgramCase "range-before-cellov-overflow-full-builder" #[]
      (fullBuilderProgramWith (.num overflowPosSigned31Bytes)),
    mkStvarint32ProgramCase "range-before-cellov-nan-full-builder" #[]
      (fullBuilderProgramWith .nan),

    -- Branch map: stack-underflow and pop/type ordering.
    mkStvarint32Case "underflow/empty" #[],
    mkStvarint32Case "underflow/one-item" #[.builder Builder.empty],
    mkStvarint32Case "underflow/one-int-only" #[intV 7],
    mkStvarint32Case "type/x-pop-first-top-not-int" #[.builder Builder.empty, .null],
    mkStvarint32Case "type/x-pop-first-top-builder" #[.null, .builder Builder.empty],
    mkStvarint32Case "type/builder-pop-second" #[intV 2, intV 1],

    mkStvarint32Case "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvarint32SetGasExact), .tonEnvOp .setGasLimit, stvarint32Instr],
    mkStvarint32Case "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvarint32SetGasExactMinusOne), .tonEnvOp .setGasLimit, stvarint32Instr],

    mkStvarint32ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStvarint32ProgramCase "program/build-1023-overflow-cellov" #[] (fullBuilderProgramWith (.num 0)),
    mkStvarint32ProgramCase "program/cellov-in-range-neg1" #[] (fullBuilderProgramWith (.num (-1))),
    mkStvarint32ProgramCase "program/cellov-in-range-max31" #[] (fullBuilderProgramWith (.num maxSigned31Bytes)),
    mkStvarint32ProgramCase "program/cellov-in-range-sample" #[] (fullBuilderProgramWith (.num samplePos))
  ]
  fuzz := #[
    { seed := 2026020922
      count := 300
      gen := genStvarint32FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STVARINT32
