import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STVARINT16

/-
STVARINT16 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stVarInt true 16)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STVARINT16` encode: `0xfa03`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa03` decode to `.stVarInt true 16`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_var_integer`, `util::store_var_integer` with `len_bits=4`, `sgnd=true`).

Branch map used for this suite:
- Lean STVARINT16 path: 12 branch sites / 16 terminal outcomes
  (`checkUnderflow 2`; kind guard; x pop/type; NaN split; builder pop/type;
   signed lenBytes derivation; len overflow guard; capacity guard; payload store path).
- C++ STVARINT16 path: 9 branch sites / 13 aligned outcomes
  (`check_underflow(2)`; x then builder pop; len range before capacity; success push).

Key risk areas:
- stack order is `... builder x` (`x` on top); `x` is popped first via `popInt`;
- len overflow (`lenBytes >= 16`) must throw `rangeChk` before any capacity check;
- for `NaN`, error is `rangeChk` before builder is popped (type/cellOv cannot win);
- exact 15-byte signed boundary must pass; 16-byte requirement must fail.
-/

private def stvarint16Id : InstrId := { name := "STVARINT16" }

private def stvarint16Instr : Instr :=
  .cellExt (.stVarInt true 16)

private def mkStvarint16Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stvarint16Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvarint16Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStvarint16ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvarint16Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStvarint16Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stvarint16Instr stack

private def runStvarint16DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStvarint16DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 424)) stack

private def maxSigned15Bytes : Int := intPow2 119 - 1

private def minSigned15Bytes : Int := -(intPow2 119)

private def overflowPosSigned15Bytes : Int := intPow2 119

private def overflowNegSigned15Bytes : Int := -(intPow2 119) - 1

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def fullBuilderProgramWith (x : IntVal) : Array Instr :=
  build1023Program ++ #[.pushInt x, stvarint16Instr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stvarint16Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num (-2)), stvarint16Instr
  ]

private def stvarint16SetGasExact : Int :=
  computeExactGasBudget stvarint16Instr

private def stvarint16SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stvarint16Instr

private def encodeSignedVarIntBits (lenBits : Nat) (n : Int) : Except Excno BitString := do
  let lenBytes : Nat := (intSignedBitSizeTwos n + 7) / 8
  let payload ← intToBitsTwos n (lenBytes * 8)
  pure (natToBits lenBytes lenBits ++ payload)

private def pickStvarint16InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then maxSigned15Bytes
    else if pick = 4 then minSigned15Bytes
    else if pick = 5 then 12345678901234567890
    else if pick = 6 then -12345678901234567890
    else 42
  (x, rng')

private def genStvarint16FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  if shape = 0 then
    let (x, rng2) := pickStvarint16InRange rng1
    (mkStvarint16Case s!"fuzz/ok/top-only/x-{x}" #[.builder Builder.empty, intV x], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStvarint16InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 103 else .cell Cell.empty
    (mkStvarint16Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, .builder Builder.empty, intV x], rng3)
  else if shape = 2 then
    (mkStvarint16Case "fuzz/range/overflow-pos" #[.builder Builder.empty, intV overflowPosSigned15Bytes], rng1)
  else if shape = 3 then
    (mkStvarint16Case "fuzz/range/overflow-neg" #[.builder Builder.empty, intV overflowNegSigned15Bytes], rng1)
  else if shape = 4 then
    (mkStvarint16Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStvarint16Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStvarint16Case "fuzz/type/x-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 7 then
    (mkStvarint16Case "fuzz/type/builder-not-builder" #[intV 2, intV 1], rng1)
  else if shape = 8 then
    (mkStvarint16ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 9 then
    let (x, rng2) := pickStvarint16InRange rng1
    (mkStvarint16ProgramCase s!"fuzz/cellov/in-range-x-{x}" #[] (fullBuilderProgramWith (.num x)), rng2)
  else
    (mkStvarint16ProgramCase "fuzz/range-before-cellov-overflow" #[]
      (fullBuilderProgramWith (.num overflowPosSigned15Bytes)), rng1)

def suite : InstrSuite where
  id := stvarint16Id
  unit := #[
    { name := "unit/direct/success-boundaries-and-encoding"
      run := do
        let checks : Array Int := #[0, 1, -1, 127, -128, maxSigned15Bytes, minSigned15Bytes]
        for x in checks do
          let bs ←
            match encodeSignedVarIntBits 4 x with
            | .ok out => pure out
            | .error e => throw (IO.userError s!"unexpected encode error {e} for x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/x-{x}"
            (runStvarint16Direct #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let bs ←
          match encodeSignedVarIntBits 4 (-2) with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let appended := prefBuilder.storeBits bs
        expectOkStack "ok/append-existing-bits"
          (runStvarint16Direct #[.builder prefBuilder, intV (-2)])
          #[.builder appended]

        let deepBits ←
          match encodeSignedVarIntBits 4 7 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let expectedDeep := Builder.empty.storeBits deepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStvarint16Direct #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks-and-order"
      run := do
        expectErr "range/overflow-pos"
          (runStvarint16Direct #[.builder Builder.empty, intV overflowPosSigned15Bytes]) .rangeChk
        expectErr "range/overflow-neg"
          (runStvarint16Direct #[.builder Builder.empty, intV overflowNegSigned15Bytes]) .rangeChk
        expectErr "range/nan"
          (runStvarint16Direct #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "error-order/range-before-cellov-overflow"
          (runStvarint16Direct #[.builder fullBuilder1023, intV overflowPosSigned15Bytes]) .rangeChk
        expectErr "error-order/range-before-cellov-nan"
          (runStvarint16Direct #[.builder fullBuilder1023, .int .nan]) .rangeChk

        expectErr "invopcode/invalid-kind-24"
          (runStvarint16DirectInstr (.cellExt (.stVarInt true 24)) #[.builder Builder.empty, intV 0]) .invOpcode }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStvarint16Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStvarint16Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStvarint16Direct #[.null]) .stkUnd

        expectErr "type/x-pop-first-top-not-int"
          (runStvarint16Direct #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/x-pop-first-top-builder"
          (runStvarint16Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/builder-pop-second"
          (runStvarint16Direct #[intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-in-range-path"
      run := do
        expectErr "cellov/full-builder-x0"
          (runStvarint16Direct #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "cellov/full-builder-xneg1"
          (runStvarint16Direct #[.builder fullBuilder1023, intV (-1)]) .cellOv
        expectErr "cellov/full-builder-x42"
          (runStvarint16Direct #[.builder fullBuilder1023, intV 42]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stvarint16Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stvarint16" s0 stvarint16Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stVarInt true 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvarint16/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvarint16/kind24: expected assemble invOpcode, got success")
        match assembleCp0 [.cellExt (.stVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvarint16/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvarint16/uint16-alias: expected assemble invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStvarint16DispatchFallback #[.null])
          #[.null, intV 424] }
  ]
  oracle := #[
    mkStvarint16Case "ok/zero" #[.builder Builder.empty, intV 0],
    mkStvarint16Case "ok/one" #[.builder Builder.empty, intV 1],
    mkStvarint16Case "ok/neg-one" #[.builder Builder.empty, intV (-1)],
    mkStvarint16Case "ok/127" #[.builder Builder.empty, intV 127],
    mkStvarint16Case "ok/minus-128" #[.builder Builder.empty, intV (-128)],
    mkStvarint16Case "ok/max-signed-15-bytes" #[.builder Builder.empty, intV maxSigned15Bytes],
    mkStvarint16Case "ok/min-signed-15-bytes" #[.builder Builder.empty, intV minSigned15Bytes],
    mkStvarint16Case "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7],
    mkStvarint16ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    mkStvarint16Case "range/overflow-pos" #[.builder Builder.empty, intV overflowPosSigned15Bytes],
    mkStvarint16Case "range/overflow-neg" #[.builder Builder.empty, intV overflowNegSigned15Bytes],
    mkStvarint16ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStvarint16ProgramCase "range-before-cellov-overflow-full-builder" #[]
      (fullBuilderProgramWith (.num overflowPosSigned15Bytes)),
    mkStvarint16ProgramCase "range-before-cellov-nan-full-builder" #[]
      (fullBuilderProgramWith .nan),

    mkStvarint16Case "underflow/empty" #[],
    mkStvarint16Case "underflow/one-item" #[.builder Builder.empty],
    mkStvarint16Case "type/x-pop-first-top-not-int" #[.builder Builder.empty, .null],
    mkStvarint16Case "type/x-pop-first-top-builder" #[.null, .builder Builder.empty],
    mkStvarint16Case "type/builder-pop-second" #[intV 2, intV 1],

    mkStvarint16Case "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvarint16SetGasExact), .tonEnvOp .setGasLimit, stvarint16Instr],
    mkStvarint16Case "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvarint16SetGasExactMinusOne), .tonEnvOp .setGasLimit, stvarint16Instr],

    mkStvarint16ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStvarint16ProgramCase "program/build-1023-overflow-cellov" #[] (fullBuilderProgramWith (.num 0)),
    mkStvarint16ProgramCase "program/cellov-in-range-neg1" #[] (fullBuilderProgramWith (.num (-1))),
    mkStvarint16ProgramCase "program/cellov-in-range-pos42" #[] (fullBuilderProgramWith (.num 42))
  ]
  fuzz := #[
    { seed := 2026020921
      count := 300
      gen := genStvarint16FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STVARINT16
