import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDVARINT32

/-
LDVARINT32 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.ldVarInt true 32)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDVARINT32` encode: `0xfa05`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa05` decode to `.cellExt (.ldVarInt true 32)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_var_integer`, `util::load_var_integer_q` with `len_bits=5`, `sgnd=true`).

Branch map used for this suite:
- Lean LDVARINT32 path: 8 branch sites / 12 terminal outcomes
  (dispatch; underflow/type on `popSlice`; kind guard; len read;
   payload-availability guard; signed decode; success push path).
- C++ LDVARINT32 path: 6 branch sites / 10 aligned outcomes.

Key risk areas:
- signed decode at 31-byte boundary (`[-2^247, 2^247 - 1]`);
- len=0 must decode to zero;
- `cellUnd` for both short 5-bit prefix and short payload;
- assembler/decode must keep `LDVARINT32` distinct from `LDVARINT16`.
-/

private def ldvarint32Id : InstrId := { name := "LDVARINT32" }

private def ldvarint32Instr : Instr :=
  .cellExt (.ldVarInt true 32)

private def mkLdvarint32Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldvarint32Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldvarint32Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdvarint32Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt ldvarint32Instr stack

private def runLdvarint32DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runLdvarint32DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 431)) stack

private def maxSigned31Bytes : Int := intPow2 247 - 1

private def minSigned31Bytes : Int := -(intPow2 247)

private def samplePos : Int := intPow2 200 + 222333

private def sampleNeg : Int := -(intPow2 200) + 333222

private def tailBits9 : BitString := natToBits 219 9

private def tailBits13 : BitString := natToBits 5001 13

private def ldvarint32SetGasExact : Int :=
  computeExactGasBudget ldvarint32Instr

private def ldvarint32SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldvarint32Instr

private def mkLdvarint32Slice (n : Int) (tailBits : BitString := #[]) : Slice :=
  match encodeSignedVarIntBits 5 n with
  | .ok payload => mkSliceFromBits (payload ++ tailBits)
  | .error _ => mkSliceFromBits #[]

private def mkTruncatedPayloadSlice (lenBytes : Nat) (payloadBits : Nat) : Slice :=
  mkSliceFromBits (natToBits lenBytes 5 ++ Array.replicate payloadBits false)

private def pickLdvarint32InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then 127
    else if pick = 4 then -128
    else if pick = 5 then maxSigned31Bytes
    else if pick = 6 then minSigned31Bytes
    else sampleNeg
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

private def genLdvarint32FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (x, rng2) := pickLdvarint32InRange rng1
    (mkLdvarint32Case s!"fuzz/ok/top-only/x-{x}" #[.slice (mkLdvarint32Slice x)], rng2)
  else if shape = 1 then
    let (x, rng2) := pickLdvarint32InRange rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdvarint32Case s!"fuzz/ok/with-tail/x-{x}" #[.slice (mkLdvarint32Slice x tail)], rng3)
  else if shape = 2 then
    let (x, rng2) := pickLdvarint32InRange rng1
    (mkLdvarint32Case s!"fuzz/ok/deep-stack/x-{x}" #[.null, .slice (mkLdvarint32Slice x)], rng2)
  else if shape = 3 then
    let (prefixBits, rng2) := randNat rng1 0 4
    (mkLdvarint32Case s!"fuzz/cellund/prefix-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng2)
  else if shape = 4 then
    let (s, rng2) := pickTruncatedPayloadSlice rng1
    (mkLdvarint32Case "fuzz/cellund/truncated-payload" #[.slice s], rng2)
  else if shape = 5 then
    (mkLdvarint32Case "fuzz/cellund/len31-prefix-only"
      #[.slice (mkTruncatedPayloadSlice 31 0)], rng1)
  else if shape = 6 then
    (mkLdvarint32Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdvarint32Case "fuzz/type/top-not-slice" #[.null], rng1)
  else if shape = 8 then
    (mkLdvarint32Case "fuzz/type/deep-top-not-slice" #[.slice (mkLdvarint32Slice 1), .null], rng1)
  else if shape = 9 then
    (mkLdvarint32Case "fuzz/ok/max-boundary" #[.slice (mkLdvarint32Slice maxSigned31Bytes)], rng1)
  else if shape = 10 then
    (mkLdvarint32Case "fuzz/cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)], rng1)
  else
    let (tail, rng2) := pickTailBits rng1
    (mkLdvarint32Case "fuzz/ok/len0-with-tail"
      #[.slice (mkSliceFromBits (natToBits 0 5 ++ tail))], rng2)

def suite : InstrSuite where
  id := ldvarint32Id
  unit := #[
    { name := "unit/direct/signed-boundaries-and-remainder"
      run := do
        let checks : Array (Int × BitString) :=
          #[
            (0, #[]),
            (1, #[]),
            (-1, #[]),
            (127, #[]),
            (-128, #[]),
            (samplePos, #[]),
            (sampleNeg, #[]),
            (maxSigned31Bytes, #[]),
            (minSigned31Bytes, #[]),
            (0, tailBits9),
            (minSigned31Bytes, tailBits13)
          ]
        for c in checks do
          let x := c.1
          let tail := c.2
          let payload ←
            match encodeSignedVarIntBits 5 x with
            | .ok bs => pure bs
            | .error e => throw (IO.userError s!"unexpected encode error {e} for x={x}")
          let input := mkSliceFromBits (payload ++ tail)
          let rem := input.advanceBits payload.size
          expectOkStack s!"ok/x-{x}/tail-{tail.size}"
            (runLdvarint32Direct #[.slice input])
            #[intV x, .slice rem]

        let inputDeep := mkLdvarint32Slice (-7) tailBits9
        let payloadDeep ←
          match encodeSignedVarIntBits 5 (-7) with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let remDeep := inputDeep.advanceBits payloadDeep.size
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdvarint32Direct #[.null, .slice inputDeep])
          #[.null, intV (-7), .slice remDeep] }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        expectErr "cellund/prefix-too-short-0"
          (runLdvarint32Direct #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "cellund/prefix-too-short-4"
          (runLdvarint32Direct #[.slice (mkSliceFromBits (Array.replicate 4 false))]) .cellUnd
        expectErr "cellund/len1-no-payload"
          (runLdvarint32Direct #[.slice (mkTruncatedPayloadSlice 1 0)]) .cellUnd
        expectErr "cellund/len2-payload-short"
          (runLdvarint32Direct #[.slice (mkTruncatedPayloadSlice 2 9)]) .cellUnd
        expectErr "cellund/len8-payload-short"
          (runLdvarint32Direct #[.slice (mkTruncatedPayloadSlice 8 63)]) .cellUnd
        expectErr "cellund/len31-prefix-only"
          (runLdvarint32Direct #[.slice (mkTruncatedPayloadSlice 31 0)]) .cellUnd
        expectErr "cellund/len31-payload-short"
          (runLdvarint32Direct #[.slice (mkTruncatedPayloadSlice 31 247)]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdvarint32Direct #[]) .stkUnd
        expectErr "type/top-not-slice" (runLdvarint32Direct #[.null]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdvarint32Direct #[.slice (mkLdvarint32Slice 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[ldvarint32Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldvarint32" s0 ldvarint32Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.ldVarInt true 16)] with
        | .ok _ => pure ()
        | .error e => throw (IO.userError s!"ldvarint32/int16-alias: expected success, got {e}")
        match assembleCp0 [.cellExt (.ldVarInt true 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldvarint32/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldvarint32/kind24: expected assemble invOpcode, got success")
        expectErr "invopcode/direct-kind24"
          (runLdvarint32DirectInstr (.cellExt (.ldVarInt true 24)) #[.slice (mkLdvarint32Slice 0)]) .invOpcode }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdvarint32DispatchFallback #[.null])
          #[.null, intV 431] }
  ]
  oracle := #[
    mkLdvarint32Case "ok/zero" #[.slice (mkLdvarint32Slice 0)],
    mkLdvarint32Case "ok/one" #[.slice (mkLdvarint32Slice 1)],
    mkLdvarint32Case "ok/neg-one" #[.slice (mkLdvarint32Slice (-1))],
    mkLdvarint32Case "ok/127" #[.slice (mkLdvarint32Slice 127)],
    mkLdvarint32Case "ok/minus-128" #[.slice (mkLdvarint32Slice (-128))],
    mkLdvarint32Case "ok/sample-pos" #[.slice (mkLdvarint32Slice samplePos)],
    mkLdvarint32Case "ok/sample-neg" #[.slice (mkLdvarint32Slice sampleNeg)],
    mkLdvarint32Case "ok/max-signed-31-bytes" #[.slice (mkLdvarint32Slice maxSigned31Bytes)],
    mkLdvarint32Case "ok/min-signed-31-bytes" #[.slice (mkLdvarint32Slice minSigned31Bytes)],
    mkLdvarint32Case "ok/len0-with-tail" #[.slice (mkSliceFromBits (natToBits 0 5 ++ tailBits9))],
    mkLdvarint32Case "ok/min-with-tail" #[.slice (mkLdvarint32Slice minSigned31Bytes tailBits13)],
    mkLdvarint32Case "ok/deep-stack-below-preserved" #[.null, .slice (mkLdvarint32Slice (-7) tailBits9)],

    mkLdvarint32Case "cellund/prefix-too-short-0" #[.slice (mkSliceFromBits #[])],
    mkLdvarint32Case "cellund/prefix-too-short-4" #[.slice (mkSliceFromBits (Array.replicate 4 false))],
    mkLdvarint32Case "cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)],
    mkLdvarint32Case "cellund/len2-payload-short" #[.slice (mkTruncatedPayloadSlice 2 9)],
    mkLdvarint32Case "cellund/len8-payload-short" #[.slice (mkTruncatedPayloadSlice 8 63)],
    mkLdvarint32Case "cellund/len31-prefix-only" #[.slice (mkTruncatedPayloadSlice 31 0)],
    mkLdvarint32Case "cellund/len31-payload-short" #[.slice (mkTruncatedPayloadSlice 31 247)],

    mkLdvarint32Case "underflow/empty" #[],
    mkLdvarint32Case "type/top-not-slice" #[.null],
    mkLdvarint32Case "type/deep-top-not-slice" #[.slice (mkLdvarint32Slice 1), .null],

    mkLdvarint32Case "gas/exact-cost-succeeds" #[.slice (mkLdvarint32Slice 7)]
      #[.pushInt (.num ldvarint32SetGasExact), .tonEnvOp .setGasLimit, ldvarint32Instr],
    mkLdvarint32Case "gas/exact-minus-one-out-of-gas" #[.slice (mkLdvarint32Slice 7)]
      #[.pushInt (.num ldvarint32SetGasExactMinusOne), .tonEnvOp .setGasLimit, ldvarint32Instr]
  ]
  fuzz := #[
    { seed := 2026020932
      count := 320
      gen := genLdvarint32FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDVARINT32
