import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STVARUINT32

/-
STVARUINT32 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.stVarInt false 32)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STVARUINT32` encode: `0xfa06`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa06` decode to `.stVarInt false 32`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_var_integer`, `util::store_var_integer` with `len_bits=5`, `sgnd=false`).

Branch map used for this suite:
- Lean STVARUINT32 path: 13 branch sites / 17 terminal outcomes
  (`checkUnderflow 2`; kind guard; x pop/type; NaN split; builder pop/type;
   unsigned negative guard; lenBytes derivation; len overflow guard; capacity guard; payload store path).
- C++ STVARUINT32 path: 10 branch sites / 14 aligned outcomes
  (`check_underflow(2)`; x then builder pop; unsigned range guard; len range before capacity).

Key risk areas:
- stack order is `... builder x` (`x` on top);
- unsigned negative fast-fail (`rangeChk`) before len/capacity;
- len overflow (`lenBytes >= 32`) throws `rangeChk` before capacity checks;
- len transition at `2^240` (`30 -> 31` payload bytes) must be encoded correctly;
- capacity boundary exact-fit (`1023` bits total) must pass; `+1` bit must fail;
- exact 31-byte unsigned boundary must pass; 32-byte requirement must fail.
-/

private def stvaruint32Id : InstrId := { name := "STVARUINT32" }

private def stvaruint32Instr : Instr :=
  .cellExt (.stVarInt false 32)

private def mkStvaruint32Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stvaruint32Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvaruint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStvaruint32ProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stvaruint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStvaruint32Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt stvaruint32Instr stack

private def runStvaruint32DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runStvaruint32DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 426)) stack

private def maxUnsigned31Bytes : Int := intPow2 248 - 1

private def overflowPosUnsigned31Bytes : Int := intPow2 248

private def maxUnsigned30Bytes : Int := intPow2 240 - 1

private def minUnsigned31Bytes : Int := intPow2 240

private def samplePos : Int := intPow2 200 + 54321

private def builderWithBits (n : Nat) : Builder :=
  Builder.empty.storeBits (Array.replicate n false)

private def nearFullLen1ExactFit : Builder := builderWithBits 1010

private def nearFullLen1Overflow : Builder := builderWithBits 1011

private def nearFullLen31ExactFit : Builder := builderWithBits 770

private def nearFullLen31Overflow : Builder := builderWithBits 771

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def fullBuilderProgramWith (x : IntVal) : Array Instr :=
  build1023Program ++ #[.pushInt x, stvaruint32Instr]

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, stvaruint32Instr]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    .pushInt (.num 17), stvaruint32Instr
  ]

private def stvaruint32SetGasExact : Int :=
  computeExactGasBudget stvaruint32Instr

private def stvaruint32SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stvaruint32Instr

private def encodeUnsignedVarIntBits (lenBits : Nat) (n : Int) : BitString :=
  let lenBytes : Nat := (natLenBits n.toNat + 7) / 8
  let payload := natToBits n.toNat (lenBytes * 8)
  natToBits lenBytes lenBits ++ payload

private def pickStvaruint32InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 255
    else if pick = 3 then 256
    else if pick = 4 then maxUnsigned30Bytes
    else if pick = 5 then minUnsigned31Bytes
    else if pick = 6 then maxUnsigned31Bytes
    else samplePos
  (x, rng')

private def genStvaruint32FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  if shape = 0 then
    let (x, rng2) := pickStvaruint32InRange rng1
    (mkStvaruint32Case s!"fuzz/ok/top-only/x-{x}" #[.builder Builder.empty, intV x], rng2)
  else if shape = 1 then
    let (x, rng2) := pickStvaruint32InRange rng1
    let (noisePick, rng3) := randNat rng2 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 109 else .cell Cell.empty
    (mkStvaruint32Case s!"fuzz/ok/deep-stack/x-{x}" #[noise, .builder Builder.empty, intV x], rng3)
  else if shape = 2 then
    (mkStvaruint32Case "fuzz/range/overflow-pos" #[.builder Builder.empty, intV overflowPosUnsigned31Bytes], rng1)
  else if shape = 3 then
    (mkStvaruint32Case "fuzz/range/negative" #[.builder Builder.empty, intV (-1)], rng1)
  else if shape = 4 then
    (mkStvaruint32Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStvaruint32Case "fuzz/underflow/one-item" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    (mkStvaruint32Case "fuzz/type/x-not-int" #[.builder Builder.empty, .null], rng1)
  else if shape = 7 then
    (mkStvaruint32Case "fuzz/type/builder-not-builder" #[intV 2, intV 1], rng1)
  else if shape = 8 then
    (mkStvaruint32ProgramCase "fuzz/range/nan-via-program" #[.builder Builder.empty] rangeNanProgram, rng1)
  else if shape = 9 then
    let (x, rng2) := pickStvaruint32InRange rng1
    (mkStvaruint32ProgramCase s!"fuzz/cellov/in-range-x-{x}" #[] (fullBuilderProgramWith (.num x)), rng2)
  else
    (mkStvaruint32ProgramCase "fuzz/range-before-cellov-overflow" #[]
      (fullBuilderProgramWith (.num overflowPosUnsigned31Bytes)), rng1)

def suite : InstrSuite where
  id := stvaruint32Id
  unit := #[
    { name := "unit/direct/success-boundaries-and-encoding"
      run := do
        -- Branch: unsigned payload size transitions (0, 1, 2, 30, 31 bytes).
        let checks : Array Int := #[0, 1, 255, 256, maxUnsigned30Bytes, minUnsigned31Bytes, samplePos, maxUnsigned31Bytes]
        for x in checks do
          let expected := Builder.empty.storeBits (encodeUnsignedVarIntBits 5 x)
          expectOkStack s!"ok/x-{x}"
            (runStvaruint32Direct #[.builder Builder.empty, intV x])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (encodeUnsignedVarIntBits 5 17)
        expectOkStack "ok/append-existing-bits"
          (runStvaruint32Direct #[.builder prefBuilder, intV 17])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (encodeUnsignedVarIntBits 5 7)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStvaruint32Direct #[.null, .builder Builder.empty, intV 7])
          #[.null, .builder expectedDeep]

        -- Branch: capacity guard exact-fit for len=1 payload (13 bits total).
        let expectedLen1Exact := nearFullLen1ExactFit.storeBits (encodeUnsignedVarIntBits 5 1)
        expectOkStack "ok/capacity-exact-fit-len1"
          (runStvaruint32Direct #[.builder nearFullLen1ExactFit, intV 1])
          #[.builder expectedLen1Exact]

        -- Branch: capacity guard exact-fit for len=31 payload (253 bits total).
        let expectedLen31Exact := nearFullLen31ExactFit.storeBits (encodeUnsignedVarIntBits 5 maxUnsigned31Bytes)
        expectOkStack "ok/capacity-exact-fit-len31"
          (runStvaruint32Direct #[.builder nearFullLen31ExactFit, intV maxUnsigned31Bytes])
          #[.builder expectedLen31Exact] }
    ,
    { name := "unit/direct/range-checks-and-order"
      run := do
        expectErr "range/overflow-pos"
          (runStvaruint32Direct #[.builder Builder.empty, intV overflowPosUnsigned31Bytes]) .rangeChk
        expectErr "range/negative"
          (runStvaruint32Direct #[.builder Builder.empty, intV (-1)]) .rangeChk
        expectErr "range/nan"
          (runStvaruint32Direct #[.builder Builder.empty, .int .nan]) .rangeChk

        expectErr "error-order/range-before-cellov-overflow"
          (runStvaruint32Direct #[.builder fullBuilder1023, intV overflowPosUnsigned31Bytes]) .rangeChk
        expectErr "error-order/range-before-cellov-negative"
          (runStvaruint32Direct #[.builder fullBuilder1023, intV (-1)]) .rangeChk
        expectErr "error-order/range-before-cellov-nan"
          (runStvaruint32Direct #[.builder fullBuilder1023, .int .nan]) .rangeChk

        expectErr "invopcode/invalid-kind-24"
          (runStvaruint32DirectInstr (.cellExt (.stVarInt false 24)) #[.builder Builder.empty, intV 0]) .invOpcode }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStvaruint32Direct #[]) .stkUnd
        expectErr "underflow/one-item" (runStvaruint32Direct #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/single-non-int" (runStvaruint32Direct #[.null]) .stkUnd

        expectErr "type/x-pop-first-top-not-int"
          (runStvaruint32Direct #[.builder Builder.empty, .null]) .typeChk
        expectErr "type/x-pop-first-top-builder"
          (runStvaruint32Direct #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/builder-pop-second"
          (runStvaruint32Direct #[intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/cellov-in-range-path"
      run := do
        expectErr "cellov/full-builder-x0"
          (runStvaruint32Direct #[.builder fullBuilder1023, intV 0]) .cellOv
        expectErr "cellov/full-builder-x1"
          (runStvaruint32Direct #[.builder fullBuilder1023, intV 1]) .cellOv
        expectErr "cellov/full-builder-xsample"
          (runStvaruint32Direct #[.builder fullBuilder1023, intV samplePos]) .cellOv
        expectErr "cellov/capacity-plus-one-len1"
          (runStvaruint32Direct #[.builder nearFullLen1Overflow, intV 1]) .cellOv
        expectErr "cellov/capacity-plus-one-len31"
          (runStvaruint32Direct #[.builder nearFullLen31Overflow, intV maxUnsigned31Bytes]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[stvaruint32Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stvaruint32" s0 stvaruint32Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.stVarInt false 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvaruint32/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvaruint32/kind24: expected assemble invOpcode, got success")
        match assembleCp0 [.cellExt (.stVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"stvaruint32/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "stvaruint32/uint16-alias: expected assemble invOpcode, got success")

        let signedNeighborCode ←
          match assembleCp0 [.cellExt (.stVarInt true 32)] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"stvaruint32/signed32-neighbor: assemble failed with {e}")
        let signedNeighborSlice := Slice.ofCell signedNeighborCode
        let signedNeighborTail ←
          expectDecodeStep "decode/stvaruint32-neighbor-signed32"
            signedNeighborSlice (.cellExt (.stVarInt true 32)) 16
        if signedNeighborTail.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/stvaruint32-neighbor-signed32: expected exhausted slice, got {signedNeighborTail.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStvaruint32DispatchFallback #[.null])
          #[.null, intV 426] }
  ]
  oracle := #[
    -- Branch: canonical success path, including lenBytes transition to 31 bytes.
    mkStvaruint32Case "ok/zero" #[.builder Builder.empty, intV 0],
    mkStvaruint32Case "ok/one" #[.builder Builder.empty, intV 1],
    mkStvaruint32Case "ok/255" #[.builder Builder.empty, intV 255],
    mkStvaruint32Case "ok/256" #[.builder Builder.empty, intV 256],
    mkStvaruint32Case "ok/max-unsigned-30-bytes" #[.builder Builder.empty, intV maxUnsigned30Bytes],
    mkStvaruint32Case "ok/min-unsigned-31-bytes" #[.builder Builder.empty, intV minUnsigned31Bytes],
    mkStvaruint32Case "ok/sample-pos" #[.builder Builder.empty, intV samplePos],
    mkStvaruint32Case "ok/max-unsigned-31-bytes" #[.builder Builder.empty, intV maxUnsigned31Bytes],
    mkStvaruint32Case "ok/capacity-exact-fit-len1" #[.builder nearFullLen1ExactFit, intV 1],
    mkStvaruint32Case "ok/capacity-exact-fit-len31" #[.builder nearFullLen31ExactFit, intV maxUnsigned31Bytes],
    mkStvaruint32Case "ok/deep-stack-below-preserved" #[.null, .builder Builder.empty, intV 7],
    mkStvaruint32ProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,

    -- Branch: range guard must fire before capacity checks for invalid x.
    mkStvaruint32Case "range/overflow-pos" #[.builder Builder.empty, intV overflowPosUnsigned31Bytes],
    mkStvaruint32Case "range/negative" #[.builder Builder.empty, intV (-1)],
    mkStvaruint32ProgramCase "range/nan-via-program" #[.builder Builder.empty] rangeNanProgram,
    mkStvaruint32ProgramCase "range-before-cellov-overflow-full-builder" #[]
      (fullBuilderProgramWith (.num overflowPosUnsigned31Bytes)),
    mkStvaruint32ProgramCase "range-before-cellov-negative-full-builder" #[]
      (fullBuilderProgramWith (.num (-1))),
    mkStvaruint32ProgramCase "range-before-cellov-nan-full-builder" #[]
      (fullBuilderProgramWith .nan),

    mkStvaruint32Case "underflow/empty" #[],
    mkStvaruint32Case "underflow/one-item" #[.builder Builder.empty],
    mkStvaruint32Case "type/x-pop-first-top-not-int" #[.builder Builder.empty, .null],
    mkStvaruint32Case "type/x-pop-first-top-builder" #[.null, .builder Builder.empty],
    mkStvaruint32Case "type/builder-pop-second" #[intV 2, intV 1],

    mkStvaruint32Case "gas/exact-cost-succeeds" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvaruint32SetGasExact), .tonEnvOp .setGasLimit, stvaruint32Instr],
    mkStvaruint32Case "gas/exact-minus-one-out-of-gas" #[.builder Builder.empty, intV 7]
      #[.pushInt (.num stvaruint32SetGasExactMinusOne), .tonEnvOp .setGasLimit, stvaruint32Instr],

    -- Branch: capacity guard on pre-filled builders (exact over-capacity).
    mkStvaruint32ProgramCase "program/build-1023-success" #[] build1023Program,
    mkStvaruint32ProgramCase "program/build-1023-overflow-cellov" #[] (fullBuilderProgramWith (.num 0)),
    mkStvaruint32ProgramCase "program/cellov-in-range-x1" #[] (fullBuilderProgramWith (.num 1)),
    mkStvaruint32ProgramCase "program/cellov-in-range-xsample" #[] (fullBuilderProgramWith (.num samplePos)),
    mkStvaruint32Case "cellov/capacity-plus-one-len1" #[.builder nearFullLen1Overflow, intV 1],
    mkStvaruint32Case "cellov/capacity-plus-one-len31" #[.builder nearFullLen31Overflow, intV maxUnsigned31Bytes]
  ]
  fuzz := #[
    { seed := 2026020923
      count := 300
      gen := genStvaruint32FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STVARUINT32
