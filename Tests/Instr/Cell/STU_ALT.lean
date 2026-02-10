import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STU_ALT

/- 
STU_ALT branch-mapping notes (fixed-width unsigned store alias, non-reversed, non-quiet):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StIntFixed.lean` (`.stIntFixed true false false bits`)
  - `TvmLean/Semantics/Exec/Cell/Stu.lean` (canonical short `STU`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf08` fixed-width decode family)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (24-bit fixed-width encoding)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_int_fixed`, `exec_store_int_common`, canonical short `STU` path).

Alias contract used in this suite:
- `STU_ALT` corresponds to fixed-width decode with flags=`001`,
  i.e. `.stIntFixed true false false bits`.
- canonical short `STU` (`0xcbxx`) executes the same unsigned/non-quiet/non-reversed path.

Branch map used for this suite:
- Lean STU_ALT path: 10 branch sites / 13 terminal outcomes
  (`checkUnderflow 2`; non-rev pop order; capacity guard; unsigned fit including NaN;
   non-quiet throws; success append).
- C++ aligned path: 8 branch sites / 11 outcomes.

Key risk areas:
- stack convention must remain `[x, builder]` (builder on top);
- `cellOv` must win before any range check when builder is full;
- unsigned boundaries at `0` and `2^bits - 1`;
- fixed 24-bit alias decode must stay aligned with short 16-bit `STU`.
-/

private def stuAltId : InstrId := { name := "STU_ALT" }

private def dispatchSentinel : Int := 53009

private def stuAltInstr (bits : Nat) : Instr :=
  .stIntFixed true false false bits

private def stuShortInstr (bits : Nat) : Instr :=
  .stu bits

private def stIntFixedWord (unsigned rev quiet : Bool) (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags3 : Nat :=
    (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
  let args11 : Nat := (flags3 <<< 8) + bits8
  let prefix13 : Nat := (0xcf08 >>> 3)
  (prefix13 <<< 11) + args11

private def stuAltWord (bits : Nat) : Nat :=
  stIntFixedWord true false false bits

private def stiAltWord (bits : Nat) : Nat :=
  stIntFixedWord false false false bits

private def stuShortWord (bits : Nat) : Nat :=
  0xcb00 + (bits - 1)

private def stiShortWord (bits : Nat) : Nat :=
  0xca00 + (bits - 1)

private def mkStuAltCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[stuAltInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStuAltProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stuAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStuAltDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStIntFixed (stuAltInstr bits) stack

private def runStuShortDirect (bits : Nat) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStu (stuShortInstr bits) stack

private def runStuAltDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStIntFixed instr (VM.push (intV dispatchSentinel)) stack

private def expectSameOutcome
    (label : String)
    (altRes shortRes : Except Excno (Array Value)) : IO Unit := do
  let same :=
    match altRes, shortRes with
    | .ok av, .ok sv => av == sv
    | .error ae, .error se => ae == se
    | _, _ => false
  if same then
    pure ()
  else
    throw (IO.userError
      s!"{label}: expected identical outcomes, got alt={reprStr altRes}, short={reprStr shortRes}")

private def maxUInt256 : Int :=
  intPow2 256 - 1

private def overUInt256 : Int :=
  intPow2 256

private def build1023Program : Array Instr :=
  build1023WithFixed stuAltInstr

private def overflowAfter1023Program : Array Instr :=
  build1023Program ++ #[.pushInt (.num 0), .xchg0 1, stuAltInstr 1]

private def cellovBeforeRangeNanProgram : Array Instr :=
  build1023Program ++ #[.pushInt .nan, .xchg0 1, stuAltInstr 1]

private def cellovBeforeRangeOverflowProgram : Array Instr :=
  build1023Program ++ #[.pushInt (.num 2), .xchg0 1, stuAltInstr 1]

private def appendExistingProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, stuAltInstr 3,
    .pushInt (.num 17), .xchg0 1, stuAltInstr 5
  ]

private def stuAltGasProbeBits : Nat := 8

private def stuAltSetGasExact : Int :=
  computeExactGasBudget (stuAltInstr stuAltGasProbeBits)

private def stuAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (stuAltInstr stuAltGasProbeBits)

private def stuAltBitsBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickStuAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stuAltBitsBoundaryPool.size - 1)
  (stuAltBitsBoundaryPool[idx]!, rng')

private def pickStuAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 2 then
    pickStuAltBitsBoundary rng1
  else
    randNat rng1 1 256

private def maxUnsignedForBits (bits : Nat) : Int :=
  intPow2 bits - 1

private def pickStuAltInRange (bits : Nat) (rng : StdGen) : Int × StdGen :=
  let maxv := maxUnsignedForBits bits
  let (pick, rng') := randNat rng 0 3
  let x : Int :=
    if pick = 0 then
      0
    else if pick = 1 then
      1
    else if pick = 2 then
      maxv
    else
      if maxv > 0 then maxv - 1 else 0
  (x, rng')

private def genStuAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (bits, rng2) := pickStuAltBitsMixed rng1
  if shape = 0 then
    let (x, rng3) := pickStuAltInRange bits rng2
    (mkStuAltCase s!"fuzz/ok/top-only/bits-{bits}" bits #[intV x, .builder Builder.empty], rng3)
  else if shape = 1 then
    let (x, rng3) := pickStuAltInRange bits rng2
    let (noisePick, rng4) := randNat rng3 0 2
    let noise : Value :=
      if noisePick = 0 then
        .null
      else if noisePick = 1 then
        intV 57
      else
        .cell Cell.empty
    (mkStuAltCase s!"fuzz/ok/deep-stack/bits-{bits}" bits #[noise, intV x, .builder Builder.empty], rng4)
  else if shape = 2 then
    (mkStuAltCase s!"fuzz/range/negative/bits-{bits}" bits #[intV (-1), .builder Builder.empty], rng2)
  else if shape = 3 then
    let overflowBits := if bits = 256 then 255 else bits
    (mkStuAltCase s!"fuzz/range/overflow/bits-{overflowBits}" overflowBits
      #[intV (intPow2 overflowBits), .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStuAltCase s!"fuzz/underflow/empty/bits-{bits}" bits #[], rng2)
  else if shape = 5 then
    (mkStuAltCase s!"fuzz/underflow/one-int/bits-{bits}" bits #[intV 1], rng2)
  else if shape = 6 then
    (mkStuAltCase s!"fuzz/underflow/one-builder/bits-{bits}" bits #[.builder Builder.empty], rng2)
  else if shape = 7 then
    (mkStuAltCase s!"fuzz/type/top-not-builder/bits-{bits}" bits #[intV 3, .null], rng2)
  else if shape = 8 then
    (mkStuAltCase s!"fuzz/type/second-not-int/bits-{bits}" bits #[.null, .builder Builder.empty], rng2)
  else if shape = 9 then
    (mkStuAltProgramCase s!"fuzz/range/nan-program/bits-{bits}"
      #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stuAltInstr bits], rng2)
  else if shape = 10 then
    let (x, rng3) := pickStuAltInRange 1 rng2
    (mkStuAltProgramCase s!"fuzz/cellov-before-range/bits-1/x-{x}" #[]
      (build1023Program ++ #[.pushInt (.num x), .xchg0 1, stuAltInstr 1]), rng3)
  else if shape = 11 then
    (mkStuAltCase "fuzz/gas/exact" stuAltGasProbeBits
      #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuAltSetGasExact), .tonEnvOp .setGasLimit, stuAltInstr stuAltGasProbeBits],
      rng2)
  else
    let (x, rng3) := pickStuAltInRange bits rng2
    (mkStuAltCase s!"fuzz/alias/short-program/bits-{bits}" bits
      #[intV x, .builder Builder.empty]
      #[stuShortInstr bits], rng3)

def suite : InstrSuite where
  id := stuAltId
  unit := #[
    { name := "unit/direct/success-boundaries-and-append"
      run := do
        let checks : Array (Nat × Int) :=
          #[
            (1, 0),
            (1, 1),
            (8, 0),
            (8, 255),
            (256, 0),
            (256, maxUInt256)
          ]
        for (bits, x) in checks do
          let expected := Builder.empty.storeBits (natToBits x.toNat bits)
          expectOkStack s!"ok/bits-{bits}/x-{x}"
            (runStuAltDirect bits #[intV x, .builder Builder.empty])
            #[.builder expected]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let appended := prefBuilder.storeBits (natToBits 17 5)
        expectOkStack "ok/append-existing-bits"
          (runStuAltDirect 5 #[intV 17, .builder prefBuilder])
          #[.builder appended]

        let expectedDeep := Builder.empty.storeBits (natToBits 7 4)
        expectOkStack "ok/deep-stack-preserve-below"
          (runStuAltDirect 4 #[.null, intV 7, .builder Builder.empty])
          #[.null, .builder expectedDeep] }
    ,
    { name := "unit/direct/range-underflow-type-order"
      run := do
        expectErr "range/nan"
          (runStuAltDirect 8 #[.int .nan, .builder Builder.empty]) .rangeChk
        expectErr "range/negative"
          (runStuAltDirect 8 #[intV (-1), .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits1"
          (runStuAltDirect 1 #[intV 2, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits8"
          (runStuAltDirect 8 #[intV 256, .builder Builder.empty]) .rangeChk
        expectErr "range/overflow-bits256"
          (runStuAltDirect 256 #[intV overUInt256, .builder Builder.empty]) .rangeChk

        expectErr "underflow/empty" (runStuAltDirect 8 #[]) .stkUnd
        expectErr "underflow/one-int" (runStuAltDirect 8 #[intV 3]) .stkUnd
        expectErr "underflow/one-builder" (runStuAltDirect 8 #[.builder Builder.empty]) .stkUnd

        expectErr "type/pop-builder-first"
          (runStuAltDirect 8 #[intV 1, .null]) .typeChk
        expectErr "type/pop-int-second"
          (runStuAltDirect 8 #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-non-int-builder-first"
          (runStuAltDirect 8 #[.cell Cell.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-before-range"
      run := do
        expectErr "cellov/full-builder"
          (runStuAltDirect 1 #[intV 0, .builder fullBuilder1023]) .cellOv
        expectErr "cellov/before-nan-range"
          (runStuAltDirect 1 #[.int .nan, .builder fullBuilder1023]) .cellOv
        expectErr "cellov/before-overflow-range"
          (runStuAltDirect 1 #[intV 2, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler"
      run := do
        let altProgram : Array Instr := #[stuAltInstr 1, stuAltInstr 256, .add]
        let altCode ←
          match assembleCp0 altProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/alt-seq failed: {e}")
        let a0 := Slice.ofCell altCode
        let a1 ← expectDecodeStep "decode/alt-1" a0 (stuAltInstr 1) 24
        let a2 ← expectDecodeStep "decode/alt-256" a1 (stuAltInstr 256) 24
        let a3 ← expectDecodeStep "decode/alt-tail-add" a2 .add 8
        if a3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/alt-end: expected exhausted slice, got {a3.bitsRemaining} bits remaining")

        let shortProgram : Array Instr := #[stuShortInstr 1, stuShortInstr 256, .add]
        let shortCode ←
          match assembleCp0 shortProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/short-seq failed: {e}")
        let s0 := Slice.ofCell shortCode
        let s1 ← expectDecodeStep "decode/short-1" s0 (stuShortInstr 1) 16
        let s2 ← expectDecodeStep "decode/short-256" s1 (stuShortInstr 256) 16
        let s3 ← expectDecodeStep "decode/short-tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/short-end: expected exhausted slice, got {s3.bitsRemaining} bits remaining")

        let alt8 ←
          match assembleCp0 [stuAltInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/alt-8 failed: {e}")
        if alt8.bits = natToBits (stuAltWord 8) 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/alt-8: expected fixed 24-bit encoding, got {alt8.bits}")
        if alt8.bits.size = 24 then
          pure ()
        else
          throw (IO.userError s!"assemble/alt-8: expected 24 bits, got {alt8.bits.size}")

        let short8 ←
          match assembleCp0 [stuShortInstr 8] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/short-8 failed: {e}")
        if short8.bits = natToBits (stuShortWord 8) 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/short-8: expected short 16-bit encoding, got {short8.bits}")
        if short8.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/short-8: expected 16 bits, got {short8.bits.size}")

        match assembleCp0 [stuAltInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/alt-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/alt-0: expected rangeChk, got success")
        match assembleCp0 [stuAltInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/alt-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/alt-257: expected rangeChk, got success")
        match assembleCp0 [stuShortInstr 0] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/short-0: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/short-0: expected rangeChk, got success")
        match assembleCp0 [stuShortInstr 257] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/short-257: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/short-257: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")

        let shortRawBits : BitString :=
          natToBits (stiShortWord 8) 16
            ++ natToBits (stuShortWord 8) 16
            ++ natToBits 0xcc 8
            ++ addCell.bits
        let sr0 := mkSliceFromBits shortRawBits
        let sr1 ← expectDecodeStep "decode/raw-sti-8-neighbor" sr0 (.sti 8) 16
        let sr2 ← expectDecodeStep "decode/raw-stu-8-short" sr1 (stuShortInstr 8) 16
        let sr3 ← expectDecodeStep "decode/raw-stref-neighbor" sr2 .stref 8
        let sr4 ← expectDecodeStep "decode/raw-short-tail-add" sr3 .add 8
        if sr4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-short-end: expected exhausted slice, got {sr4.bitsRemaining} bits remaining")

        let fixedRawCode : Cell :=
          Cell.mkOrdinary
            (natToBits 0xcf07 16 ++
             natToBits (stuAltWord 1) 24 ++
             natToBits (stiAltWord 8) 24 ++
             natToBits (stuAltWord 256) 24 ++
             natToBits 0xcf10 16 ++
             addCell.bits) #[]
        let f0 := Slice.ofCell fixedRawCode
        let f1 ← expectDecodeStep "decode/raw-boundary-stuxrq" f0 (.stIntVar true true true) 16
        let f2 ← expectDecodeStep "decode/raw-alt-stu-1" f1 (stuAltInstr 1) 24
        let f3 ← expectDecodeStep "decode/raw-fixed-sti-neighbor" f2 (.stIntFixed false false false 8) 24
        let f4 ← expectDecodeStep "decode/raw-alt-stu-256" f3 (stuAltInstr 256) 24
        let f5 ← expectDecodeStep "decode/raw-boundary-stref-alt" f4 .stref 16
        let f6 ← expectDecodeStep "decode/raw-fixed-tail-add" f5 .add 8
        if f6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-fixed-end: expected exhausted slice, got {f6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/alias-equivalence/fixed-alt-vs-short-stu"
      run := do
        let okChecks : Array (Nat × Int) :=
          #[
            (1, 1),
            (8, 0xa5),
            (32, intPow2 31),
            (256, maxUInt256)
          ]
        for (bits, x) in okChecks do
          expectSameOutcome s!"align/ok/bits-{bits}"
            (runStuAltDirect bits #[intV x, .builder Builder.empty])
            (runStuShortDirect bits #[intV x, .builder Builder.empty])

        expectSameOutcome "align/range/nan"
          (runStuAltDirect 8 #[.int .nan, .builder Builder.empty])
          (runStuShortDirect 8 #[.int .nan, .builder Builder.empty])
        expectSameOutcome "align/range/negative"
          (runStuAltDirect 8 #[intV (-1), .builder Builder.empty])
          (runStuShortDirect 8 #[intV (-1), .builder Builder.empty])
        expectSameOutcome "align/range/overflow"
          (runStuAltDirect 8 #[intV 256, .builder Builder.empty])
          (runStuShortDirect 8 #[intV 256, .builder Builder.empty])
        expectSameOutcome "align/underflow/empty"
          (runStuAltDirect 8 #[])
          (runStuShortDirect 8 #[])
        expectSameOutcome "align/type/top-not-builder"
          (runStuAltDirect 8 #[intV 1, .null])
          (runStuShortDirect 8 #[intV 1, .null])
        expectSameOutcome "align/type/second-not-int"
          (runStuAltDirect 8 #[.null, .builder Builder.empty])
          (runStuShortDirect 8 #[.null, .builder Builder.empty])
        expectSameOutcome "align/cellov/full-builder"
          (runStuAltDirect 1 #[intV 0, .builder fullBuilder1023])
          (runStuShortDirect 1 #[intV 0, .builder fullBuilder1023])

        let mappingBits : Array Nat := #[1, 8, 255, 256]
        for bits in mappingBits do
          let altSlice := mkSliceFromBits (natToBits (stuAltWord bits) 24)
          let shortSlice := mkSliceFromBits (natToBits (stuShortWord bits) 16)

          let decodedAlt ←
            match decodeCp0WithBits altSlice with
            | .ok (instr, used, _) =>
                if used = 24 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/alt/bits-{bits}: expected 24-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/alt/bits-{bits}: failed with {e}")
          let decodedShort ←
            match decodeCp0WithBits shortSlice with
            | .ok (instr, used, _) =>
                if used = 16 then
                  pure instr
                else
                  throw (IO.userError s!"decode/map/short/bits-{bits}: expected 16-bit decode, got {used}")
            | .error e =>
                throw (IO.userError s!"decode/map/short/bits-{bits}: failed with {e}")

          if decodedAlt == stuAltInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/alt/bits-{bits}: unexpected instruction {reprStr decodedAlt}")
          if decodedShort == stuShortInstr bits then
            pure ()
          else
            throw (IO.userError s!"decode/map/short/bits-{bits}: unexpected instruction {reprStr decodedShort}")

          let x : Int :=
            if bits = 1 then
              1
            else if bits = 8 then
              0xa5
            else if bits = 255 then
              intPow2 254
            else
              maxUInt256
          expectSameOutcome s!"align/decoded/bits-{bits}"
            (runHandlerDirect execInstrCellStIntFixed decodedAlt #[intV x, .builder Builder.empty])
            (runHandlerDirect execInstrCellStu decodedShort #[intV x, .builder Builder.empty]) }
    ,
    { name := "unit/dispatch/non-stintfixed-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runStuAltDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/short-stu-neighbor"
          (runStuAltDispatchFallback (stuShortInstr 8) #[intV 11, .builder Builder.empty])
          #[intV 11, .builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/stintvar-neighbor"
          (runStuAltDispatchFallback (.stIntVar true false false) #[.cell Cell.empty])
          #[.cell Cell.empty, intV dispatchSentinel] }
  ]
  oracle := #[
    mkStuAltCase "ok/bits-1/zero" 1 #[intV 0, .builder Builder.empty],
    mkStuAltCase "ok/bits-1/one" 1 #[intV 1, .builder Builder.empty],
    mkStuAltCase "ok/bits-8/max" 8 #[intV 255, .builder Builder.empty],
    mkStuAltCase "ok/bits-32/max" 32 #[intV (intPow2 32 - 1), .builder Builder.empty],
    mkStuAltCase "ok/bits-255/max" 255 #[intV (intPow2 255 - 1), .builder Builder.empty],
    mkStuAltCase "ok/bits-256/max" 256 #[intV maxUInt256, .builder Builder.empty],
    mkStuAltCase "ok/deep-stack-preserve" 4 #[.null, intV 7, .builder Builder.empty],
    mkStuAltProgramCase "ok/append-existing-bits-via-program" #[] appendExistingProgram,
    mkStuAltProgramCase "program/build-1023-success" #[] build1023Program,

    mkStuAltCase "range/negative" 8 #[intV (-1), .builder Builder.empty],
    mkStuAltCase "range/overflow-bits-1" 1 #[intV 2, .builder Builder.empty],
    mkStuAltCase "range/overflow-bits-8" 8 #[intV 256, .builder Builder.empty],
    mkStuAltCase "range/overflow-bits-255" 255 #[intV (intPow2 255), .builder Builder.empty],
    mkStuAltCase "range/negative-bits-256" 256 #[intV (-1), .builder Builder.empty],
    mkStuAltProgramCase "range/nan-via-program" #[.builder Builder.empty]
      #[.pushInt .nan, .xchg0 1, stuAltInstr 8],

    mkStuAltCase "underflow/empty" 8 #[],
    mkStuAltCase "underflow/one-int" 8 #[intV 1],
    mkStuAltCase "type/top-not-builder" 8 #[intV 1, .null],
    mkStuAltCase "type/second-not-int" 8 #[.null, .builder Builder.empty],

    mkStuAltCase "gas/exact-cost-succeeds" stuAltGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuAltSetGasExact), .tonEnvOp .setGasLimit, stuAltInstr stuAltGasProbeBits],
    mkStuAltCase "gas/exact-minus-one-out-of-gas" stuAltGasProbeBits #[intV 7, .builder Builder.empty]
      #[.pushInt (.num stuAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, stuAltInstr stuAltGasProbeBits],

    mkStuAltProgramCase "program/build-1023-overflow-cellov" #[] overflowAfter1023Program,
    mkStuAltProgramCase "program/cellov-before-range-nan" #[] cellovBeforeRangeNanProgram,
    mkStuAltProgramCase "program/cellov-before-range-overflow" #[] cellovBeforeRangeOverflowProgram
  ]
  fuzz := #[
    { seed := 2026021107
      count := 320
      gen := genStuAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STU_ALT
