import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDGRAMS

/-
LDGRAMS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/LdGrams.lean`
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDGRAMS` encode: `0xfa00`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa00` decode to `.tonEnvOp .ldGrams`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_var_integer`, `util::load_var_integer_q` with `len_bits=4`, `sgnd=false`).

Branch map used for this suite:
- Lean LDGRAMS path: 7 branch sites / 10 terminal outcomes
  (opcode guard; pop slice underflow/type; 4-bit len read; payload-availability guard;
   success path pushing `x` and advanced slice).
- C++ LDGRAMS path: 6 branch sites / 9 aligned outcomes
  (`pop_cellslice`; `fetch_uint_to` and `fetch_int256_to`; `cell_und` on parse failure; success push).

Key risk areas:
- strict stack type/underflow ordering (`popSlice` happens first);
- `cellUnd` must trigger for short prefix and short payload cases;
- len=0 (`0000`) must decode to zero with no payload consumption;
- remainder slice must advance by exactly `4 + len*8` bits.
-/

private def ldgramsId : InstrId := { name := "LDGRAMS" }

private def ldgramsInstr : Instr :=
  .tonEnvOp .ldGrams

private def mkLdgramsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldgramsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldgramsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdgramsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvLdGrams ldgramsInstr stack

private def runLdgramsDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvLdGrams .add (VM.push (intV 428)) stack

private def mkSliceFromBits (bs : BitString) : Slice :=
  Slice.ofCell (Builder.empty.storeBits bs).finalize

private def mkLdgramsSlice (x : Int) (tailBits : BitString := #[]) : Slice :=
  mkSliceFromBits (encodeUnsignedVarIntBits 4 x ++ tailBits)

private def mkTruncatedPayloadSlice (lenBytes : Nat) (payloadBits : Nat) : Slice :=
  mkSliceFromBits (natToBits lenBytes 4 ++ Array.replicate payloadBits false)

private def maxUnsigned15Bytes : Int := maxUnsignedByBytes 15

private def samplePos : Int := intPow2 96 + 271828

private def tailBits7 : BitString := natToBits 93 7

private def tailBits11 : BitString := natToBits 1337 11

private def ldgramsSetGasExact : Int :=
  computeExactGasBudget ldgramsInstr

private def ldgramsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldgramsInstr

private def pickLdgramsInRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then 255
    else if pick = 3 then 256
    else if pick = 4 then maxUnsigned15Bytes
    else samplePos
  (x, rng')

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 12
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickTruncatedPayloadSlice (rng0 : StdGen) : Slice × StdGen :=
  let (lenBytes, rng1) := randNat rng0 1 15
  let needBits : Nat := lenBytes * 8
  let (payloadBits, rng2) := randNat rng1 0 (needBits - 1)
  (mkTruncatedPayloadSlice lenBytes payloadBits, rng2)

private def genLdgramsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (x, rng2) := pickLdgramsInRange rng1
    (mkLdgramsCase s!"fuzz/ok/top-only/x-{x}" #[.slice (mkLdgramsSlice x)], rng2)
  else if shape = 1 then
    let (x, rng2) := pickLdgramsInRange rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdgramsCase s!"fuzz/ok/with-tail/x-{x}" #[.slice (mkLdgramsSlice x tail)], rng3)
  else if shape = 2 then
    let (x, rng2) := pickLdgramsInRange rng1
    (mkLdgramsCase s!"fuzz/ok/deep-stack/x-{x}" #[.null, .slice (mkLdgramsSlice x)], rng2)
  else if shape = 3 then
    let (prefixBits, rng2) := randNat rng1 0 3
    (mkLdgramsCase s!"fuzz/cellund/prefix-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng2)
  else if shape = 4 then
    let (s, rng2) := pickTruncatedPayloadSlice rng1
    (mkLdgramsCase "fuzz/cellund/truncated-payload" #[.slice s], rng2)
  else if shape = 5 then
    (mkLdgramsCase "fuzz/cellund/len15-prefix-only"
      #[.slice (mkTruncatedPayloadSlice 15 0)], rng1)
  else if shape = 6 then
    (mkLdgramsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdgramsCase "fuzz/type/top-not-slice" #[.null], rng1)
  else if shape = 8 then
    (mkLdgramsCase "fuzz/type/deep-top-not-slice" #[.slice (mkLdgramsSlice 1), .null], rng1)
  else if shape = 9 then
    (mkLdgramsCase "fuzz/ok/max-boundary" #[.slice (mkLdgramsSlice maxUnsigned15Bytes)], rng1)
  else if shape = 10 then
    (mkLdgramsCase "fuzz/cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)], rng1)
  else
    let (tail, rng2) := pickTailBits rng1
    (mkLdgramsCase "fuzz/ok/len0-with-tail"
      #[.slice (mkSliceFromBits (natToBits 0 4 ++ tail))], rng2)

def suite : InstrSuite where
  id := ldgramsId
  unit := #[
    { name := "unit/direct/success-boundaries-and-remainder"
      run := do
        let checks : Array (Int × BitString) :=
          #[
            (0, #[]),
            (1, #[]),
            (255, #[]),
            (256, #[]),
            (samplePos, #[]),
            (maxUnsigned15Bytes, #[]),
            (0, tailBits7),
            (maxUnsigned15Bytes, tailBits11)
          ]
        for c in checks do
          let x := c.1
          let tail := c.2
          let payload := encodeUnsignedVarIntBits 4 x
          let input := mkSliceFromBits (payload ++ tail)
          let rem := input.advanceBits payload.size
          expectOkStack s!"ok/x-{x}/tail-{tail.size}"
            (runLdgramsDirect #[.slice input])
            #[intV x, .slice rem]

        let inputDeep := mkSliceFromBits (encodeUnsignedVarIntBits 4 7 ++ tailBits7)
        let remDeep := inputDeep.advanceBits (encodeUnsignedVarIntBits 4 7).size
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdgramsDirect #[.null, .slice inputDeep])
          #[.null, intV 7, .slice remDeep] }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        expectErr "cellund/prefix-too-short-0"
          (runLdgramsDirect #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "cellund/prefix-too-short-3"
          (runLdgramsDirect #[.slice (mkSliceFromBits (Array.replicate 3 false))]) .cellUnd
        expectErr "cellund/len1-no-payload"
          (runLdgramsDirect #[.slice (mkTruncatedPayloadSlice 1 0)]) .cellUnd
        expectErr "cellund/len2-payload-short"
          (runLdgramsDirect #[.slice (mkTruncatedPayloadSlice 2 9)]) .cellUnd
        expectErr "cellund/len4-payload-short"
          (runLdgramsDirect #[.slice (mkTruncatedPayloadSlice 4 31)]) .cellUnd
        expectErr "cellund/len15-prefix-only"
          (runLdgramsDirect #[.slice (mkTruncatedPayloadSlice 15 0)]) .cellUnd
        expectErr "cellund/len15-payload-short"
          (runLdgramsDirect #[.slice (mkTruncatedPayloadSlice 15 119)]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdgramsDirect #[]) .stkUnd
        expectErr "type/top-not-slice" (runLdgramsDirect #[.null]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdgramsDirect #[.slice (mkLdgramsSlice 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[ldgramsInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldgrams" s0 ldgramsInstr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.ldVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldgrams/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldgrams/uint16-alias: expected assemble invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-tonenv-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdgramsDispatchFallback #[.null])
          #[.null, intV 428] }
  ]
  oracle := #[
    mkLdgramsCase "ok/zero" #[.slice (mkLdgramsSlice 0)],
    mkLdgramsCase "ok/one" #[.slice (mkLdgramsSlice 1)],
    mkLdgramsCase "ok/255" #[.slice (mkLdgramsSlice 255)],
    mkLdgramsCase "ok/256" #[.slice (mkLdgramsSlice 256)],
    mkLdgramsCase "ok/sample-pos" #[.slice (mkLdgramsSlice samplePos)],
    mkLdgramsCase "ok/max-unsigned-15-bytes" #[.slice (mkLdgramsSlice maxUnsigned15Bytes)],
    mkLdgramsCase "ok/len0-with-tail" #[.slice (mkSliceFromBits (natToBits 0 4 ++ tailBits7))],
    mkLdgramsCase "ok/max-with-tail" #[.slice (mkLdgramsSlice maxUnsigned15Bytes tailBits11)],
    mkLdgramsCase "ok/deep-stack-below-preserved" #[.null, .slice (mkLdgramsSlice 7 tailBits7)],

    mkLdgramsCase "cellund/prefix-too-short-0" #[.slice (mkSliceFromBits #[])],
    mkLdgramsCase "cellund/prefix-too-short-3" #[.slice (mkSliceFromBits (Array.replicate 3 false))],
    mkLdgramsCase "cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)],
    mkLdgramsCase "cellund/len2-payload-short" #[.slice (mkTruncatedPayloadSlice 2 9)],
    mkLdgramsCase "cellund/len4-payload-short" #[.slice (mkTruncatedPayloadSlice 4 31)],
    mkLdgramsCase "cellund/len15-prefix-only" #[.slice (mkTruncatedPayloadSlice 15 0)],
    mkLdgramsCase "cellund/len15-payload-short" #[.slice (mkTruncatedPayloadSlice 15 119)],

    mkLdgramsCase "underflow/empty" #[],
    mkLdgramsCase "type/top-not-slice" #[.null],
    mkLdgramsCase "type/deep-top-not-slice" #[.slice (mkLdgramsSlice 1), .null],

    mkLdgramsCase "gas/exact-cost-succeeds" #[.slice (mkLdgramsSlice 7)]
      #[.pushInt (.num ldgramsSetGasExact), .tonEnvOp .setGasLimit, ldgramsInstr],
    mkLdgramsCase "gas/exact-minus-one-out-of-gas" #[.slice (mkLdgramsSlice 7)]
      #[.pushInt (.num ldgramsSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldgramsInstr]
  ]
  fuzz := #[
    { seed := 2026020929
      count := 320
      gen := genLdgramsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDGRAMS
