import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDVARINT16

/-
LDVARINT16 branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Ext.lean` (`.cellExt (.ldVarInt true 16)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDVARINT16` encode: `0xfa01`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa01` decode to `.cellExt (.ldVarInt true 16)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_var_integer`, `util::load_var_integer_q` with `len_bits=4`, `sgnd=true`).

Branch map used for this suite:
- Lean LDVARINT16 path: 8 branch sites / 12 terminal outcomes
  (dispatch; underflow/type on `popSlice`; kind guard to `lenBits`; len read;
   payload-availability guard; signed decode; success push path).
- C++ LDVARINT16 path: 6 branch sites / 10 aligned outcomes
  (`pop_cellslice`; deserialize checks; `cell_und` on short input; success push).

Key risk areas:
- signed two's-complement decode at 1-byte and 15-byte boundaries;
- len=0 (`0000`) must decode to zero;
- `cellUnd` must cover both short-prefix and short-payload failures;
- assembler/decode must map only the dedicated `0xfa01` opcode.
-/

private def ldvarint16Id : InstrId := { name := "LDVARINT16" }

private def ldvarint16Instr : Instr :=
  .cellExt (.ldVarInt true 16)

private def mkLdvarint16Case
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldvarint16Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldvarint16Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdvarint16Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt ldvarint16Instr stack

private def runLdvarint16DirectInstr (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellExt instr stack

private def runLdvarint16DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellExt .add (VM.push (intV 429)) stack

private def maxSigned15Bytes : Int := intPow2 119 - 1

private def minSigned15Bytes : Int := -(intPow2 119)

private def samplePos : Int := intPow2 80 + 54321

private def sampleNeg : Int := -(intPow2 80) + 12345

private def tailBits7 : BitString := natToBits 111 7

private def tailBits11 : BitString := natToBits 777 11

private def ldvarint16SetGasExact : Int :=
  computeExactGasBudget ldvarint16Instr

private def ldvarint16SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldvarint16Instr

private def mkLdvarint16Slice (n : Int) (tailBits : BitString := #[]) : Slice :=
  match encodeSignedVarIntBits 4 n with
  | .ok payload => mkSliceFromBits (payload ++ tailBits)
  | .error _ => mkSliceFromBits #[]

private def mkTruncatedPayloadSlice (lenBytes : Nat) (payloadBits : Nat) : Slice :=
  mkSliceFromBits (natToBits lenBytes 4 ++ Array.replicate payloadBits false)

private def pickLdvarint16InRange (rng : StdGen) : Int × StdGen :=
  let (pick, rng') := randNat rng 0 7
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then 127
    else if pick = 4 then -128
    else if pick = 5 then maxSigned15Bytes
    else if pick = 6 then minSigned15Bytes
    else sampleNeg
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

private def genLdvarint16FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (x, rng2) := pickLdvarint16InRange rng1
    (mkLdvarint16Case s!"fuzz/ok/top-only/x-{x}" #[.slice (mkLdvarint16Slice x)], rng2)
  else if shape = 1 then
    let (x, rng2) := pickLdvarint16InRange rng1
    let (tail, rng3) := pickTailBits rng2
    (mkLdvarint16Case s!"fuzz/ok/with-tail/x-{x}" #[.slice (mkLdvarint16Slice x tail)], rng3)
  else if shape = 2 then
    let (x, rng2) := pickLdvarint16InRange rng1
    (mkLdvarint16Case s!"fuzz/ok/deep-stack/x-{x}" #[.null, .slice (mkLdvarint16Slice x)], rng2)
  else if shape = 3 then
    let (prefixBits, rng2) := randNat rng1 0 3
    (mkLdvarint16Case s!"fuzz/cellund/prefix-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng2)
  else if shape = 4 then
    let (s, rng2) := pickTruncatedPayloadSlice rng1
    (mkLdvarint16Case "fuzz/cellund/truncated-payload" #[.slice s], rng2)
  else if shape = 5 then
    (mkLdvarint16Case "fuzz/cellund/len15-prefix-only"
      #[.slice (mkTruncatedPayloadSlice 15 0)], rng1)
  else if shape = 6 then
    (mkLdvarint16Case "fuzz/underflow/empty" #[], rng1)
  else if shape = 7 then
    (mkLdvarint16Case "fuzz/type/top-not-slice" #[.null], rng1)
  else if shape = 8 then
    (mkLdvarint16Case "fuzz/type/deep-top-not-slice" #[.slice (mkLdvarint16Slice 1), .null], rng1)
  else if shape = 9 then
    (mkLdvarint16Case "fuzz/ok/max-boundary" #[.slice (mkLdvarint16Slice maxSigned15Bytes)], rng1)
  else if shape = 10 then
    (mkLdvarint16Case "fuzz/cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)], rng1)
  else
    let (tail, rng2) := pickTailBits rng1
    (mkLdvarint16Case "fuzz/ok/len0-with-tail"
      #[.slice (mkSliceFromBits (natToBits 0 4 ++ tail))], rng2)

def suite : InstrSuite where
  id := ldvarint16Id
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
            (maxSigned15Bytes, #[]),
            (minSigned15Bytes, #[]),
            (0, tailBits7),
            (minSigned15Bytes, tailBits11)
          ]
        for c in checks do
          let x := c.1
          let tail := c.2
          let payload ←
            match encodeSignedVarIntBits 4 x with
            | .ok bs => pure bs
            | .error e => throw (IO.userError s!"unexpected encode error {e} for x={x}")
          let input := mkSliceFromBits (payload ++ tail)
          let rem := input.advanceBits payload.size
          expectOkStack s!"ok/x-{x}/tail-{tail.size}"
            (runLdvarint16Direct #[.slice input])
            #[intV x, .slice rem]

        let inputDeep := mkLdvarint16Slice (-7) tailBits7
        let payloadDeep ←
          match encodeSignedVarIntBits 4 (-7) with
          | .ok bs => pure bs
          | .error e => throw (IO.userError s!"unexpected encode error {e}")
        let remDeep := inputDeep.advanceBits payloadDeep.size
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdvarint16Direct #[.null, .slice inputDeep])
          #[.null, intV (-7), .slice remDeep] }
    ,
    { name := "unit/direct/cellund-branches"
      run := do
        expectErr "cellund/prefix-too-short-0"
          (runLdvarint16Direct #[.slice (mkSliceFromBits #[])]) .cellUnd
        expectErr "cellund/prefix-too-short-3"
          (runLdvarint16Direct #[.slice (mkSliceFromBits (Array.replicate 3 false))]) .cellUnd
        expectErr "cellund/len1-no-payload"
          (runLdvarint16Direct #[.slice (mkTruncatedPayloadSlice 1 0)]) .cellUnd
        expectErr "cellund/len2-payload-short"
          (runLdvarint16Direct #[.slice (mkTruncatedPayloadSlice 2 9)]) .cellUnd
        expectErr "cellund/len4-payload-short"
          (runLdvarint16Direct #[.slice (mkTruncatedPayloadSlice 4 31)]) .cellUnd
        expectErr "cellund/len15-prefix-only"
          (runLdvarint16Direct #[.slice (mkTruncatedPayloadSlice 15 0)]) .cellUnd
        expectErr "cellund/len15-payload-short"
          (runLdvarint16Direct #[.slice (mkTruncatedPayloadSlice 15 119)]) .cellUnd }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdvarint16Direct #[]) .stkUnd
        expectErr "type/top-not-slice" (runLdvarint16Direct #[.null]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdvarint16Direct #[.slice (mkLdvarint16Slice 1), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[ldvarint16Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldvarint16" s0 ldvarint16Instr 16
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        match assembleCp0 [.cellExt (.ldVarInt false 16)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldvarint16/uint16-alias: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldvarint16/uint16-alias: expected assemble invOpcode, got success")
        match assembleCp0 [.cellExt (.ldVarInt true 24)] with
        | .error .invOpcode => pure ()
        | .error e => throw (IO.userError s!"ldvarint16/kind24: expected invOpcode, got {e}")
        | .ok _ => throw (IO.userError "ldvarint16/kind24: expected assemble invOpcode, got success") }
    ,
    { name := "unit/dispatch/non-cellext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdvarint16DispatchFallback #[.null])
          #[.null, intV 429] }
  ]
  oracle := #[
    mkLdvarint16Case "ok/zero" #[.slice (mkLdvarint16Slice 0)],
    mkLdvarint16Case "ok/one" #[.slice (mkLdvarint16Slice 1)],
    mkLdvarint16Case "ok/neg-one" #[.slice (mkLdvarint16Slice (-1))],
    mkLdvarint16Case "ok/127" #[.slice (mkLdvarint16Slice 127)],
    mkLdvarint16Case "ok/minus-128" #[.slice (mkLdvarint16Slice (-128))],
    mkLdvarint16Case "ok/sample-pos" #[.slice (mkLdvarint16Slice samplePos)],
    mkLdvarint16Case "ok/sample-neg" #[.slice (mkLdvarint16Slice sampleNeg)],
    mkLdvarint16Case "ok/max-signed-15-bytes" #[.slice (mkLdvarint16Slice maxSigned15Bytes)],
    mkLdvarint16Case "ok/min-signed-15-bytes" #[.slice (mkLdvarint16Slice minSigned15Bytes)],
    mkLdvarint16Case "ok/len0-with-tail" #[.slice (mkSliceFromBits (natToBits 0 4 ++ tailBits7))],
    mkLdvarint16Case "ok/min-with-tail" #[.slice (mkLdvarint16Slice minSigned15Bytes tailBits11)],
    mkLdvarint16Case "ok/deep-stack-below-preserved" #[.null, .slice (mkLdvarint16Slice (-7) tailBits7)],

    mkLdvarint16Case "cellund/prefix-too-short-0" #[.slice (mkSliceFromBits #[])],
    mkLdvarint16Case "cellund/prefix-too-short-3" #[.slice (mkSliceFromBits (Array.replicate 3 false))],
    mkLdvarint16Case "cellund/len1-no-payload" #[.slice (mkTruncatedPayloadSlice 1 0)],
    mkLdvarint16Case "cellund/len2-payload-short" #[.slice (mkTruncatedPayloadSlice 2 9)],
    mkLdvarint16Case "cellund/len4-payload-short" #[.slice (mkTruncatedPayloadSlice 4 31)],
    mkLdvarint16Case "cellund/len15-prefix-only" #[.slice (mkTruncatedPayloadSlice 15 0)],
    mkLdvarint16Case "cellund/len15-payload-short" #[.slice (mkTruncatedPayloadSlice 15 119)],

    mkLdvarint16Case "underflow/empty" #[],
    mkLdvarint16Case "type/top-not-slice" #[.null],
    mkLdvarint16Case "type/deep-top-not-slice" #[.slice (mkLdvarint16Slice 1), .null],

    mkLdvarint16Case "gas/exact-cost-succeeds" #[.slice (mkLdvarint16Slice 7)]
      #[.pushInt (.num ldvarint16SetGasExact), .tonEnvOp .setGasLimit, ldvarint16Instr],
    mkLdvarint16Case "gas/exact-minus-one-out-of-gas" #[.slice (mkLdvarint16Slice 7)]
      #[.pushInt (.num ldvarint16SetGasExactMinusOne), .tonEnvOp .setGasLimit, ldvarint16Instr]
  ]
  fuzz := #[
    { seed := 2026020930
      count := 320
      gen := genLdvarint16FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDVARINT16
