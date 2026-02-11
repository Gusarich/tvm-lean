import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDVARUINT32

/-
LDVARUINT32 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.ldVarInt false 32)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDVARUINT32` encode: `0xfa04`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa04` decode to `.cellExt (.ldVarInt false 32)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_var_integer`, `util::load_var_integer_q` with `len_bits=5`, `sgnd=false`).

Branch map used for this suite:
- Lean LDVARUINT32 path: 8 branch sites / 12 terminal outcomes
  (dispatch; underflow/type on `popSlice`; kind guard; len read;
   payload-availability guard; unsigned decode; success push path).
- C++ LDVARUINT32 path: 6 branch sites / 10 aligned outcomes.

Key risk areas:
- unsigned decode at 31-byte boundary (`2^248 - 1`);
- len=0 must decode to zero;
- `cellUnd` for both short 5-bit prefix and short payload;
- opcode mapping must use only `0xfa04` for this AST form.
-/

private def ldvaruint32Id : InstrId := { name := "LDVARUINT32" }

private def ldvaruint32Instr : Instr :=
  .cellExt (.ldVarInt false 32)

private def mkLdvaruint32Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldvaruint32Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldvaruint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdvaruint32Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt ldvaruint32Instr stack

private def runLdvaruint32DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runLdvaruint32DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 430)) stack

private def maxUnsigned31Bytes : Int := maxUnsignedByBytes 31

private def maxUnsigned2Bytes : Int := maxUnsignedByBytes 2

private def minUnsigned3Bytes : Int := intPow2 16

private def maxUnsigned4Bytes : Int := maxUnsignedByBytes 4

private def minUnsigned5Bytes : Int := intPow2 32

private def maxUnsigned30Bytes : Int := maxUnsignedByBytes 30

private def minUnsigned31Bytes : Int := intPow2 240

private def samplePos : Int := intPow2 200 + 654321

private def tailBits9 : BitString := natToBits 341 9

private def ldvaruint32SetGasExact : Int :=
  computeExactGasBudget ldvaruint32Instr

private def ldvaruint32SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldvaruint32Instr

private def mkLdvaruint32Slice (n : Int) (tailBits : BitString := #[]) : Slice :=
  mkSliceFromBits (encodeUnsignedVarIntBits 5 n ++ tailBits)

private def mkTruncatedPayloadSlice (lenBytes : Nat) (payloadBits : Nat) : Slice :=
  mkSliceFromBits (natToBits lenBytes 5 ++ Array.replicate payloadBits false)

private def pickLdvaruint32InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 9
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 255
    else if pick = 3 then 256
    else if pick = 4 then samplePos
    else if pick = 5 then maxUnsigned2Bytes
    else if pick = 6 then minUnsigned3Bytes
    else if pick = 7 then maxUnsigned4Bytes
    else if pick = 8 then minUnsigned31Bytes
    else maxUnsigned31Bytes
  (x, rng')

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 14
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickTruncatedPayloadSlice (rng0 : StdGen) : Slice × StdGen :=
  let (lenBytes, rng1) := randNat rng0 1 31
  let needBits : Nat := lenBytes * 8
  let (payloadBits, rng2) := randNat rng1 0 (needBits - 1)
  (mkTruncatedPayloadSlice lenBytes payloadBits, rng2)

private def genLdvaruint32FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (x, rng2) := pickLdvaruint32InRange rng1
    (mkLdvaruint32Case s!"fuzz/ok/top-only/x-{x}" #[.slice (mkLdvaruint32Slice x)], rng2)
  else if shape = 1 then
    let (x, rng2) := pickLdvaruint32InRange rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdvaruint32Case s!"fuzz/ok/with-tail/x-{x}" #[.slice (mkLdvaruint32Slice x tail)], rng3)
  else if shape = 2 then
    let (x, rng2) := pickLdvaruint32InRange rng1
    (mkLdvaruint32Case s!"fuzz/ok/deep-stack/x-{x}" #[.null, .slice (mkLdvaruint32Slice x)], rng2)
  else if shape = 3 then
    let (prefixBits, rng2) := randNat rng1 0 4
    (mkLdvaruint32Case s!"fuzz/cellund/prefix-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng2)
  else if shape = 4 then
    let (s, rng2) := pickTruncatedPayloadSlice rng1
    (mkLdvaruint32Case "fuzz/cellund/truncated-payload" #[.slice s], rng2)
  else if shape = 5 then
    (mkLdvaruint32Case "fuzz/cellund/len31-prefix-only"
      #[.slice (mkTruncatedPayloadSlice 31 0)], rng1)
  else if shape = 6 then
    (mkLdvaruint32Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdvaruint32Case "fuzz/type/top-not-slice" #[.null], rng1)
  else if shape = 8 then
    (mkLdvaruint32Case "fuzz/type/deep-top-not-slice" #[.slice (mkLdvaruint32Slice 1), .null], rng1)
  else if shape = 9 then
    (mkLdvaruint32Case "fuzz/ok/max-boundary" #[.slice (mkLdvaruint32Slice maxUnsigned31Bytes)], rng1)
  else if shape = 10 then
    (mkLdvaruint32Case "fuzz/cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)], rng1)
  else
    let (tail, rng2) := pickTailBits rng1
    (mkLdvaruint32Case "fuzz/ok/len0-with-tail"
      #[.slice (mkSliceFromBits (natToBits 0 5 ++ tail))], rng2)

def suite : InstrSuite where
  id := ldvaruint32Id
  unit := #[
    { name := "unit/direct/unsigned-boundaries-and-remainder"
      run := do
        -- Branch map: successful len decode -> unsigned payload decode -> push int + remainder.
        let checks : Array (Int × BitString) :=
          #[
            (0, #[]),
            (1, #[]),
            (255, #[]),
            (256, #[]),
            (maxUnsigned2Bytes, #[]),
            (minUnsigned3Bytes, #[]),
            (maxUnsigned4Bytes, #[]),
            (minUnsigned5Bytes, #[]),
            (samplePos, #[]),
            (maxUnsigned30Bytes, #[]),
            (minUnsigned31Bytes, #[]),
            (maxUnsigned31Bytes, #[]),
            (0, tailBits9),
            (minUnsigned31Bytes, tailBits13),
            (maxUnsigned31Bytes, tailBits13)
          ]
        for c in checks do
          let x := c.1
          let tail := c.2
          let payload := encodeUnsignedVarIntBits 5 x
          let input := mkSliceFromBits (payload ++ tail)
          let rem := input.advanceBits payload.size
          expectOkStack s!"ok/x-{x}/tail-{tail.size}"
            (runLdvaruint32Direct #[.slice input])
            #[intV x, .slice rem]

        let inputDeep := mkLdvaruint32Slice 7 tailBits9
        let remDeep := inputDeep.advanceBits (encodeUnsignedVarIntBits 5 7).size
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdvaruint32Direct #[.null, .slice inputDeep])
          #[.null, intV 7, .slice remDeep] }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        -- Branch map: cell underflow from short 5-bit len prefix and short declared payload.
        expectErr "cellund/prefix-too-short-0"
          (runLdvaruint32Direct #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "cellund/prefix-too-short-1"
          (runLdvaruint32Direct #[.slice (mkSliceFromBits (Array.replicate 1 false))]) .cellUnd
        expectErr "cellund/prefix-too-short-2"
          (runLdvaruint32Direct #[.slice (mkSliceFromBits (Array.replicate 2 false))]) .cellUnd
        expectErr "cellund/prefix-too-short-4"
          (runLdvaruint32Direct #[.slice (mkSliceFromBits (Array.replicate 4 false))]) .cellUnd
        expectErr "cellund/len1-no-payload"
          (runLdvaruint32Direct #[.slice (mkTruncatedPayloadSlice 1 0)]) .cellUnd
        expectErr "cellund/len2-payload-short"
          (runLdvaruint32Direct #[.slice (mkTruncatedPayloadSlice 2 9)]) .cellUnd
        expectErr "cellund/len8-payload-short"
          (runLdvaruint32Direct #[.slice (mkTruncatedPayloadSlice 8 63)]) .cellUnd
        expectErr "cellund/len31-prefix-only"
          (runLdvaruint32Direct #[.slice (mkTruncatedPayloadSlice 31 0)]) .cellUnd
        expectErr "cellund/len31-payload-short"
          (runLdvaruint32Direct #[.slice (mkTruncatedPayloadSlice 31 247)]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        -- Branch map: popSlice ordering (underflow first, then type check on top stack value).
        expectErr "underflow/empty" (runLdvaruint32Direct #[]) .stkUnd
        expectErr "type/top-not-slice" (runLdvaruint32Direct #[.null]) .typeChk
        expectErr "type/top-int" (runLdvaruint32Direct #[intV 7]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdvaruint32Direct #[.slice (mkLdvaruint32Slice 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        -- Branch map: cp0 opcode encode/decode boundary + non-LDVARUINT32 rejection.
        let program : Array Instr := #[ldvaruint32Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldvaruint32" s0 ldvaruint32Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.ldVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldvaruint32/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldvaruint32/uint16-alias: expected assemble invOpcode, got success")
        match assembleCp0 [.cellExt (.ldVarInt false 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldvaruint32/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldvaruint32/kind24: expected assemble invOpcode, got success")
        -- kind=16 is valid (LDVARUINT16 / LDGRAMS alias), verify it succeeds
        let kind16Input := mkLdvaruint32Slice 0
        expectOkStack "ok/direct-kind16-varuint16"
          (runLdvaruint32DirectInstr (.cellExt (.ldVarInt false 16)) #[.slice kind16Input])
          #[intV 0, .slice (kind16Input.advanceBits 4)]
        expectErr "invopcode/direct-kind24"
          (runLdvaruint32DirectInstr (.cellExt (.ldVarInt false 24)) #[.slice (mkLdvaruint32Slice 0)]) .invOpcode }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdvaruint32DispatchFallback #[.null])
          #[.null, intV 430] }
  ]
  oracle := #[
    -- Branch map: success decode path (len/payload boundaries + remainder preservation).
    mkLdvaruint32Case "ok/zero" #[.slice (mkLdvaruint32Slice 0)],
    mkLdvaruint32Case "ok/one" #[.slice (mkLdvaruint32Slice 1)],
    mkLdvaruint32Case "ok/255" #[.slice (mkLdvaruint32Slice 255)],
    mkLdvaruint32Case "ok/256" #[.slice (mkLdvaruint32Slice 256)],
    mkLdvaruint32Case "ok/2-byte-max-65535" #[.slice (mkLdvaruint32Slice maxUnsigned2Bytes)],
    mkLdvaruint32Case "ok/3-byte-min-65536" #[.slice (mkLdvaruint32Slice minUnsigned3Bytes)],
    mkLdvaruint32Case "ok/4-byte-max-u32" #[.slice (mkLdvaruint32Slice maxUnsigned4Bytes)],
    mkLdvaruint32Case "ok/5-byte-min-u33" #[.slice (mkLdvaruint32Slice minUnsigned5Bytes)],
    mkLdvaruint32Case "ok/sample-pos" #[.slice (mkLdvaruint32Slice samplePos)],
    mkLdvaruint32Case "ok/max-unsigned-30-bytes" #[.slice (mkLdvaruint32Slice maxUnsigned30Bytes)],
    mkLdvaruint32Case "ok/min-unsigned-31-bytes" #[.slice (mkLdvaruint32Slice minUnsigned31Bytes)],
    mkLdvaruint32Case "ok/max-unsigned-31-bytes" #[.slice (mkLdvaruint32Slice maxUnsigned31Bytes)],
    mkLdvaruint32Case "ok/len0-with-tail" #[.slice (mkSliceFromBits (natToBits 0 5 ++ tailBits9))],
    mkLdvaruint32Case "ok/max-with-tail" #[.slice (mkLdvaruint32Slice maxUnsigned31Bytes tailBits13)],
    mkLdvaruint32Case "ok/deep-stack-below-preserved" #[.null, .slice (mkLdvaruint32Slice 7 tailBits9)],

    -- Branch map: cell underflow from short prefix and truncated payload branches.
    mkLdvaruint32Case "cellund/prefix-too-short-0" #[.slice (mkSliceFromBits #[])],
    mkLdvaruint32Case "cellund/prefix-too-short-1" #[.slice (mkSliceFromBits (Array.replicate 1 false))],
    mkLdvaruint32Case "cellund/prefix-too-short-2" #[.slice (mkSliceFromBits (Array.replicate 2 false))],
    mkLdvaruint32Case "cellund/prefix-too-short-4" #[.slice (mkSliceFromBits (Array.replicate 4 false))],
    mkLdvaruint32Case "cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)],
    mkLdvaruint32Case "cellund/len2-payload-short" #[.slice (mkTruncatedPayloadSlice 2 9)],
    mkLdvaruint32Case "cellund/len8-payload-short" #[.slice (mkTruncatedPayloadSlice 8 63)],
    mkLdvaruint32Case "cellund/len31-prefix-only" #[.slice (mkTruncatedPayloadSlice 31 0)],
    mkLdvaruint32Case "cellund/len31-payload-short" #[.slice (mkTruncatedPayloadSlice 31 247)],

    -- Branch map: stack pop/type guard ordering.
    mkLdvaruint32Case "underflow/empty" #[],
    mkLdvaruint32Case "type/top-not-slice" #[.null],
    mkLdvaruint32Case "type/top-int" #[intV 7],
    mkLdvaruint32Case "type/deep-top-not-slice" #[.slice (mkLdvaruint32Slice 1), .null],

    -- Branch map: gas metering pass/fail boundaries for LDVARUINT32 execution.
    mkLdvaruint32Case "gas/exact-cost-succeeds" #[.slice (mkLdvaruint32Slice 7)]
      #[.pushInt (.num ldvaruint32SetGasExact), .tonEnvOp .setGasLimit, ldvaruint32Instr],
    mkLdvaruint32Case "gas/exact-minus-one-out-of-gas" #[.slice (mkLdvaruint32Slice 7)]
      #[.pushInt (.num ldvaruint32SetGasExactMinusOne), .tonEnvOp .setGasLimit, ldvaruint32Instr]
  ]
  fuzz := #[
    { seed := 2026020931
      count := 320
      gen := genLdvaruint32FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDVARUINT32
