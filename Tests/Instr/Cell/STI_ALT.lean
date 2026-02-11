import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STI_ALT

/-
STI_ALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean`
    (`.stIntFixed unsigned=false rev=false quiet=false bits`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf08 >> 3` fixed-width family decode to `.stIntFixed`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.stIntFixed` encode; width range check `1..256`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, opcode table `0xcf08 >> 3`)

Branch map used for this suite (`STI_ALT` only):
- `checkUnderflow 2`;
- non-rev pop order (`builder` top, `int` second);
- capacity guard (`canExtendBy bits`) with non-quiet `cellOv`;
- signed-fit split (`NaN` / out-of-range => `rangeChk`);
- success append.

Alias/decode contract covered here:
- `STI_ALT` is the 24-bit fixed-width form (`0xcf08` family, flags `000`);
- canonical `STI` is the 16-bit immediate form (`0xca`);
- both produce aligned outcomes on equivalent stacks for `bits ∈ [1,256]`.
-/

private def stiAltId : InstrId := { name := "STI_ALT" }

private def stiAltInstr (bits : Nat) : Instr :=
  .stIntFixed false false false bits

private def stiInstr (bits : Nat) : Instr :=
  .sti bits

private def mkStiAltCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stiAltInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStiAltProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stiAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStiAltDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stiAltInstr bits) stack

private def runStiCanonicalDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSti (stiInstr bits) stack

private def runStiAltDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed .add (VM.push (intV 417)) stack

private def expectSameOutcome
    (label : String)
    (lhs rhs : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match lhs, rhs with
    | .ok lv, .ok rv => lv == rv
    | .error le, .error re => le == re
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got lhs={reprStr lhs}, rhs={reprStr rhs}")

private def minSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else -(intPow2 (bits - 1))

private def maxSignedBits (bits : Nat) : Int :=
  if bits = 0 then 0 else intPow2 (bits - 1) - 1

private def overflowPosSignedBits (bits : Nat) : Int :=
  if bits = 0 then 1 else intPow2 (bits - 1)

private def overflowNegSignedBits (bits : Nat) : Int :=
  if bits = 0 then -1 else -(intPow2 (bits - 1)) - 1

private def minStiAlt256 : Int :=
  minSignedBits 256

private def maxStiAlt256 : Int :=
  maxSignedBits 256

private def overMaxStiAlt256 : Int :=
  overflowPosSignedBits 256

private def underMinStiAlt256 : Int :=
  overflowNegSignedBits 256

private def storeIntFixedWord (unsigned rev quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xcf08 >>> 3)
  (prefix13 <<< 11) + args11

private def stiAltWord (bits : Nat) : Nat :=
  storeIntFixedWord false false false bits

private def stiWord (bits : Nat) : Nat :=
  0xca00 + (bits - 1)

private def build1023Program : Array Instr :=
  build1023WithFixed stiAltInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stiAltInstr 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stiAltInstr 1]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 1), .xchg0 1, stiAltInstr 1]

private def stiAltGasProbeBits : Nat := 8

private def stiAltSetGasExact : Int :=
  computeExactGasBudget (stiAltInstr stiAltGasProbeBits)

private def stiAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stiAltInstr stiAltGasProbeBits)

private def stiAltBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStiAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stiAltBitsBoundaryPool.size - 1)
  (stiAltBitsBoundaryPool[idx]!, rng')

private def pickStiAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStiAltBitsBoundary rng1
  else
    randNat rng1 1 256

private def pickStiAltInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let lo := minSignedBits bits
  let hi := maxSignedBits bits
  let (pick, rng') := randNat rng 0 5
  let x : Int :=
    if pick = 0 then 0
    else if pick = 1 then 1
    else if pick = 2 then -1
    else if pick = 3 then hi
    else if pick = 4 then lo
    else if hi > lo then hi - 1 else lo
  (x, rng')

private def genStiAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 10
  let (bits, rng2) := pickStiAltBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStiAltInRange bits rng2
    (mkStiAltCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStiAltInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then .null else if noisePick = 1 then intV 83 else .cell Cell.empty
    (mkStiAltCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    (mkStiAltCase s!"fuzz/range/overflow-pos/bits-{bits}" bits
      #[intV (overflowPosSignedBits bits), .builder Builder.empty], rng2)
  else if shape = 3 then
    (mkStiAltCase s!"fuzz/range/overflow-neg/bits-{bits}" bits
      #[intV (overflowNegSignedBits bits), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStiAltCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStiAltCase s!"fuzz/underflow/one-int/bits-{bits}" bits #[intV 5], rng2)
  else if shape = 6 then
    (mkStiAltCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[intV 3, .null], rng2)
  else if shape = 7 then
    (mkStiAltCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else if shape = 8 then
    (mkStiAltProgramCase s!"fuzz/range/nan-via-program/bits-{bits}" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stiAltInstr bits], rng2)
  else if shape = 9 then
    (mkStiAltProgramCase "fuzz/cellov/build1023-then-store" #[] overflowAfter1023Program, rng2)
  else
    let (useExact, rng3) := randBool rng2
    if useExact then
      (mkStiAltCase "fuzz/gas/exact" stiAltGasProbeBits #[intV 7, .builder Builder.empty]
        #[.pushInt (.num stiAltSetGasExact), .tonEnvOp .setGasLimit, stiAltInstr stiAltGasProbeBits], rng3)
    else
      (mkStiAltCase "fuzz/gas/exact-minus-one" stiAltGasProbeBits #[intV 7, .builder Builder.empty]
        #[.pushInt (.num stiAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, stiAltInstr stiAltGasProbeBits], rng3)

def suite : InstrSuite where
  id := stiAltId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, -1),
            (1, 0),
            (8, -128),
            (8, 127),
            (256, minStiAlt256),
            (256, maxStiAlt256)
          ]
        for c in checks do
          let bits := c.1
          let x := c.2
          let bs ←
            match intToBitsTwos x bits with
            | .ok out => pure out
            | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e} for bits={bits}, x={x}")
          let expected := Builder.empty.storeBits bs
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStiAltDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appendedBits ←
          match intToBitsTwos (-3) 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let appended := prefBuilder.storeBits appendedBits
        expectOkStack "ok/append-existing-bits"
          (runStiAltDirect 4 #[intV (-3), .builder prefBuilder])
          #[.builder appended]

        let expectedDeepBits ←
          match intToBitsTwos 7 4 with
          | .ok out => pure out
          | .error e => throw (IO.userError s!"unexpected intToBitsTwos error {e}")
        let expectedDeep := Builder.empty.storeBits expectedDeepBits
        expectOkStack "ok/deep-stack-preserve-below"
          (runStiAltDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-checks"
      run := do
        expectErr "range/overflow-pos-bits1"
          (runStiAltDirect 1 #[intV 1, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits1"
          (runStiAltDirect 1 #[intV (-2), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-bits8"
          (runStiAltDirect 8 #[intV 128, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits8"
          (runStiAltDirect 8 #[intV (-129), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-pos-bits256"
          (runStiAltDirect 256 #[intV overMaxStiAlt256, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-neg-bits256"
          (runStiAltDirect 256 #[intV underMinStiAlt256, .builder Builder.empty]) .rangeChk
        expectErr "range/nan"
          (runStiAltDirect 8 #[.int .nan, .builder Builder.empty]) .rangeChk }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStiAltDirect 8 #[]) .stkUnd
        expectErr "underflow/one-int" (runStiAltDirect 8 #[intV 3]) .stkUnd
        expectErr "underflow/one-builder" (runStiAltDirect 8 #[.builder Builder.empty]) .stkUnd

        expectErr "type/pop-builder-first"
          (runStiAltDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/pop-int-second"
          (runStiAltDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-pop-builder-first"
          (runStiAltDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-int-range"
      run := do
        expectErr "cellov/full-builder"
          (runStiAltDirect 1 #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-nan-range"
          (runStiAltDirect 1 #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "error-order/cellov-before-overflow-range"
          (runStiAltDirect 1 #[intV 1, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-boundaries-and-sti-equivalence"
      run := do
        let altProgram : Array Instr := #[stiAltInstr 1, stiAltInstr 256, .add]
        let altCode ←
          match assembleCp0 altProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble STI_ALT sequence failed: {e}")
        let a0 := Slice.ofCell altCode
        let a1 ← expectDecodeStep "decode/sti-alt-1" a0 (stiAltInstr 1) 24
        let a2 ← expectDecodeStep "decode/sti-alt-256" a1 (stiAltInstr 256) 24
        let a3 ← expectDecodeStep "decode/sti-alt-tail-add" a2 .add 8
        if a3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sti-alt-end: expected exhausted slice, got {a3.bitsRemaining} bits remaining")

        let stiProgram : Array Instr := #[stiInstr 1, stiInstr 256, .add]
        let stiCode ←
          match assembleCp0 stiProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble STI sequence failed: {e}")
        let s0 := Slice.ofCell stiCode
        let s1 ← expectDecodeStep "decode/sti-1" s0 (stiInstr 1) 16
        let s2 ← expectDecodeStep "decode/sti-256" s1 (stiInstr 256) 16
        let s3 ← expectDecodeStep "decode/sti-tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/sti-end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        let altWord1Code ←
          match assembleCp0 [stiAltInstr 1] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble STI_ALT 1 failed: {e}")
        if altWord1Code.bits = natToBits (stiAltWord 1) 24 then
          pure ()
        else
          throw (IO.userError s!"sti_alt/1 word mismatch: got bits {altWord1Code.bits}")

        let altWord256Code ←
          match assembleCp0 [stiAltInstr 256] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble STI_ALT 256 failed: {e}")
        if altWord256Code.bits = natToBits (stiAltWord 256) 24 then
          pure ()
        else
          throw (IO.userError s!"sti_alt/256 word mismatch: got bits {altWord256Code.bits}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let mixedSlice := mkSliceFromBits (natToBits (stiAltWord 8) 24 ++ natToBits (stiWord 8) 16 ++ addCell.bits)
        let m1 ← expectDecodeStep "decode/mixed-sti-alt-8" mixedSlice (stiAltInstr 8) 24
        let m2 ← expectDecodeStep "decode/mixed-sti-8" m1 (stiInstr 8) 16
        let m3 ← expectDecodeStep "decode/mixed-tail-add" m2 .add 8
        if m3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/mixed-end: expected exhausted slice, got {m3.bitsRemaining} bits remaining")

        match assembleCp0 [stiAltInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sti_alt/0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sti_alt/0: expected assemble rangeChk, got success")
        match assembleCp0 [stiAltInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"sti_alt/257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "sti_alt/257: expected assemble rangeChk, got success")

        expectSameOutcome "eq/success"
          (runStiAltDirect 8 #[intV 42, .builder Builder.empty])
          (runStiCanonicalDirect 8 #[intV 42, .builder Builder.empty])
        expectSameOutcome "eq/range-overflow"
          (runStiAltDirect 8 #[intV 128, .builder Builder.empty])
          (runStiCanonicalDirect 8 #[intV 128, .builder Builder.empty])
        expectSameOutcome "eq/range-nan"
          (runStiAltDirect 8 #[.int .nan, .builder Builder.empty])
          (runStiCanonicalDirect 8 #[.int .nan, .builder Builder.empty])
        expectSameOutcome "eq/underflow"
          (runStiAltDirect 8 #[])
          (runStiCanonicalDirect 8 #[])
        expectSameOutcome "eq/type-top-not-builder"
          (runStiAltDirect 8 #[intV 1, .null])
          (runStiCanonicalDirect 8 #[intV 1, .null])
        expectSameOutcome "eq/cellov-before-range"
          (runStiAltDirect 1 #[intV 1, .builder fullBuilder1023])
          (runStiCanonicalDirect 1 #[intV 1, .builder fullBuilder1023]) }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStiAltDispatchFallback #[.null])
          #[.null, intV 417] }
  ]
  oracle := #[
    mkStiAltCase "ok/bits1-min" 1 #[intV (-1), .builder Builder.empty],
    mkStiAltCase "ok/bits1-max" 1 #[intV 0, .builder Builder.empty],
    mkStiAltCase "ok/bits8-min" 8 #[intV (-128), .builder Builder.empty],
    mkStiAltCase "ok/bits8-max" 8 #[intV 127, .builder Builder.empty],
    mkStiAltCase "ok/bits16-min" 16 #[intV (-32768), .builder Builder.empty],
    mkStiAltCase "ok/bits16-max" 16 #[intV 32767, .builder Builder.empty],
    mkStiAltCase "ok/bits256-min" 256 #[intV minStiAlt256, .builder Builder.empty],
    mkStiAltCase "ok/bits256-max" 256 #[intV maxStiAlt256, .builder Builder.empty],
    mkStiAltCase "ok/deep-stack-below-preserved" 4 #[.null, intV 7, .builder Builder.empty],

    mkStiAltCase "range/overflow-pos-bits1" 1 #[intV 1, .builder Builder.empty],
    mkStiAltCase "range/overflow-neg-bits1" 1 #[intV (-2), .builder Builder.empty],
    mkStiAltCase "range/overflow-pos-bits8" 8 #[intV 128, .builder Builder.empty],
    mkStiAltCase "range/overflow-neg-bits8" 8 #[intV (-129), .builder Builder.empty],
    mkStiAltCase "range/overflow-pos-bits256" 256 #[intV overMaxStiAlt256, .builder Builder.empty],
    mkStiAltCase "range/overflow-neg-bits256" 256 #[intV underMinStiAlt256, .builder Builder.empty],
    mkStiAltProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stiAltInstr 8],

    mkStiAltCase "underflow/empty" 8 #[],
    mkStiAltCase "underflow/one-int" 8 #[intV 3],
    mkStiAltCase "type/top-not-builder" 8 #[intV 1, .null],
    mkStiAltCase "type/second-not-int" 8 #[.null, .builder Builder.empty],

    mkStiAltCase "gas/exact-cost-succeeds" stiAltGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiAltSetGasExact), .tonEnvOp .setGasLimit, stiAltInstr stiAltGasProbeBits],
    mkStiAltCase "gas/exact-minus-one-out-of-gas" stiAltGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stiAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, stiAltInstr stiAltGasProbeBits],

    mkStiAltProgramCase "program/build-1023-success" #[] build1023Program,
    mkStiAltProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStiAltProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStiAltProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026021103
      count := 500
      gen := genStiAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STI_ALT
