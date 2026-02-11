import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSLICE_ALT

/-
STSLICE_ALT branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/StSlice.lean` (`.stSlice false false`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xcf12` and canonical `0xce` decode to `.stSlice false false`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`.stSlice false false` assembles canonically as `0xce`, not `0xcf12`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_store_slice(..., quiet=false)` for both opcode entries `0xce` and `0xcf12`).

Branch map used for this suite (`STSLICE_ALT` only):
- Lean STSLICE path: 6 branch sites / 8 terminal outcomes
  (dispatch guard; `checkUnderflow 2`; top builder pop/type; second slice pop/type;
   capacity check on remaining slice bits/refs; success or `cellOv`).
- C++ STSLICE path: 5 branch sites / 7 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop_cellslice`; `can_extend_by`;
   success append or `cell_ov`).

Key risk areas:
- non-reversed stack order is `... slice builder` (builder on top);
- stored payload is exactly `slice.toCellRemaining` (respects `bitPos` / `refPos`);
- overflow checks both bits and refs at once (`canExtendBy(c.bits.size, c.refs.size)`);
- alias decode `0xcf12` must execute identically to canonical `0xce`;
- assembler must continue emitting canonical `0xce`;
- exact gas edge for `PUSHINT n; SETGASLIMIT; STSLICE`.

Oracle-shape hygiene:
- oracle `initStack` uses only supported token shapes
  (ints/null/full slices/empty builders);
- richer non-empty builders/slices are produced through `program` prelude only.
-/

private def stsliceAltId : InstrId := { name := "STSLICE_ALT" }

private def stsliceInstr : Instr := .stSlice false false

private def stsliceAltAliasOpcode : Nat := 0xcf12

private def stsliceCanonicalOpcode : Nat := 0xce

private def mkStsliceAltCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stsliceInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStsliceAltProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stsliceAltId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStsliceAltDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellStSlice stsliceInstr stack

private def runStsliceAltDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellStSlice .add (VM.push (intV 53010)) stack

private def stsliceAltSetGasExact : Int :=
  computeExactGasBudget stsliceInstr

private def stsliceAltSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stsliceInstr

private def appendOneEmptyCellRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneEmptyCellRefToTopBuilder

private def mkBuilderProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkCellProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[.endc]

private def mkSliceProgram
    (bits refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkCellProgram bits refs x ++ #[.ctos]

private def mkStsliceProgram
    (srcBits srcRefs dstBits dstRefs : Nat)
    (srcX : IntVal := .num 0)
    (dstX : IntVal := .num 0) : Array Instr :=
  mkSliceProgram srcBits srcRefs srcX
    ++ mkBuilderProgram dstBits dstRefs dstX
    ++ #[stsliceInstr]

private def stsliceAltAppendProgram : Array Instr :=
  mkStsliceProgram 5 1 3 1 (.num 17) (.num 5)

private def stsliceAltAppendWithRefsProgram : Array Instr :=
  mkStsliceProgram 4 2 7 1 (.num 9) (.num 3)

private def stsliceAltBitsBoundarySuccessProgram : Array Instr :=
  mkStsliceProgram 1 0 1022 0

private def stsliceAltRefsBoundarySuccessProgram : Array Instr :=
  mkStsliceProgram 0 1 0 3

private def stsliceAltCellOvBitsProgram : Array Instr :=
  mkStsliceProgram 1 0 1023 0

private def stsliceAltCellOvRefsProgram : Array Instr :=
  mkStsliceProgram 0 1 0 4

private def stsliceAltCellOvBothProgram : Array Instr :=
  mkStsliceProgram 1 1 1023 4

private def stsliceAltBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 63]

private def pickStsliceAltBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stsliceAltBitsBoundaryPool.size - 1)
  (stsliceAltBitsBoundaryPool[idx]!, rng')

private def pickStsliceAltBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickStsliceAltBitsBoundary rng1
  else
    randNat rng1 0 63

private def pickStsliceAltSourceRefs (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 2

private def pickStsliceAltNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let noise : Value :=
    if pick = 0 then .null else if pick = 1 then intV 109 else .cell Cell.empty
  (noise, rng')

private def genStsliceAltFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkStsliceAltCase "fuzz/ok/direct/minimal"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty], rng1)
  else if shape = 1 then
    let (noise, rng2) := pickStsliceAltNoise rng1
    (mkStsliceAltCase "fuzz/ok/direct/deep-stack"
      #[noise, .slice (Slice.ofCell Cell.empty), .builder Builder.empty], rng2)
  else if shape = 2 then
    (mkStsliceAltCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 3 then
    (mkStsliceAltCase "fuzz/underflow/one-slice" #[.slice (Slice.ofCell Cell.empty)], rng1)
  else if shape = 4 then
    (mkStsliceAltCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 5 then
    (mkStsliceAltCase "fuzz/type/top-not-builder"
      #[.slice (Slice.ofCell Cell.empty), .null], rng1)
  else if shape = 6 then
    (mkStsliceAltCase "fuzz/type/second-not-slice"
      #[.null, .builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStsliceAltCase "fuzz/type/both-wrong" #[intV 1, .null], rng1)
  else if shape = 8 then
    let (srcBits, rng2) := pickStsliceAltBitsMixed rng1
    let (srcRefs, rng3) := pickStsliceAltSourceRefs rng2
    let maxDstBits : Nat := Nat.min 63 (1023 - srcBits)
    let (dstBits, rng4) := randNat rng3 0 maxDstBits
    let (dstRefs, rng5) := randNat rng4 0 (4 - srcRefs)
    (mkStsliceAltProgramCase
      s!"fuzz/ok/program/src-b{srcBits}-r{srcRefs}-dst-b{dstBits}-r{dstRefs}"
      #[]
      (mkStsliceProgram srcBits srcRefs dstBits dstRefs),
      rng5)
  else if shape = 9 then
    let (srcBits, rng2) := randNat rng1 1 4
    (mkStsliceAltProgramCase
      s!"fuzz/ok/program/bits-boundary/src-{srcBits}-dst-{1023 - srcBits}"
      #[]
      (mkStsliceProgram srcBits 0 (1023 - srcBits) 0),
      rng2)
  else if shape = 10 then
    let (srcBits, rng2) := pickStsliceAltBitsMixed rng1
    let (dstBits, rng3) := randNat rng2 0 (Nat.min 63 (1023 - srcBits))
    (mkStsliceAltProgramCase
      s!"fuzz/ok/program/refs-boundary/src-b{srcBits}-r1-dst-b{dstBits}-r3"
      #[]
      (mkStsliceProgram srcBits 1 dstBits 3),
      rng3)
  else if shape = 11 then
    let (srcBits, rng2) := randNat rng1 1 16
    (mkStsliceAltProgramCase
      s!"fuzz/cellov/program/bits/src-{srcBits}-dst-1023"
      #[]
      (mkStsliceProgram srcBits 0 1023 0),
      rng2)
  else if shape = 12 then
    let (srcRefs, rng2) := randNat rng1 1 2
    let (srcBits, rng3) := pickStsliceAltBitsMixed rng2
    (mkStsliceAltProgramCase
      s!"fuzz/cellov/program/refs/src-b{srcBits}-r{srcRefs}-dst-r4"
      #[]
      (mkStsliceProgram srcBits srcRefs 0 4),
      rng3)
  else if shape = 13 then
    let (useExact, rng2) := randBool rng1
    if useExact then
      (mkStsliceAltCase "fuzz/gas/exact"
        #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
        #[.pushInt (.num stsliceAltSetGasExact), .tonEnvOp .setGasLimit, stsliceInstr], rng2)
    else
      (mkStsliceAltCase "fuzz/gas/exact-minus-one"
        #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
        #[.pushInt (.num stsliceAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceInstr], rng2)
  else if shape = 14 then
    let (noise, rng2) := pickStsliceAltNoise rng1
    let (srcBits, rng3) := pickStsliceAltBitsMixed rng2
    let (srcRefs, rng4) := pickStsliceAltSourceRefs rng3
    let maxDstBits : Nat := Nat.min 31 (1023 - srcBits)
    let (dstBits, rng5) := randNat rng4 0 maxDstBits
    let (dstRefs, rng6) := randNat rng5 0 (4 - srcRefs)
    (mkStsliceAltProgramCase
      s!"fuzz/ok/program/noise/src-b{srcBits}-r{srcRefs}-dst-b{dstBits}-r{dstRefs}"
      #[noise]
      (mkStsliceProgram srcBits srcRefs dstBits dstRefs),
      rng6)
  else
    (mkStsliceAltProgramCase "fuzz/cellov/program/bits-and-refs" #[] stsliceAltCellOvBothProgram, rng1)

def suite : InstrSuite where
  id := stsliceAltId
  unit := #[
    { name := "unit/direct/stack-order-remaining-slice-and-success"
      run := do
        expectOkStack "ok/empty-slice-noop"
          (runStsliceAltDirect #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty])
          #[.builder Builder.empty]

        let existingRef : Cell := Cell.mkOrdinary (natToBits 3 2) #[]
        let sourceTailRef : Cell := Cell.mkOrdinary (natToBits 1 1) #[]
        let sourceCell : Cell := Cell.mkOrdinary (natToBits 21 5) #[sourceTailRef]
        let sourceSlice := Slice.ofCell sourceCell
        let prefBuilder : Builder := { bits := natToBits 6 3, refs := #[existingRef] }
        let expectedPref : Builder :=
          { bits := prefBuilder.bits ++ sourceCell.bits
            refs := prefBuilder.refs ++ sourceCell.refs }
        expectOkStack "ok/non-empty-append-bits-and-refs-tail"
          (runStsliceAltDirect #[.slice sourceSlice, .builder prefBuilder])
          #[.builder expectedPref]

        let partialBase : Cell := Cell.mkOrdinary (natToBits 45 6) #[Cell.empty, sourceTailRef]
        let partialSlice : Slice := { (Slice.ofCell partialBase) with bitPos := 2, refPos := 1 }
        let rem := partialSlice.toCellRemaining
        let bPartial : Builder := { bits := natToBits 2 2, refs := #[Cell.empty] }
        let expectedPartial : Builder :=
          { bits := bPartial.bits ++ rem.bits
            refs := bPartial.refs ++ rem.refs }
        expectOkStack "ok/uses-toCellRemaining-not-full-cell"
          (runStsliceAltDirect #[.slice partialSlice, .builder bPartial])
          #[.builder expectedPartial]

        let consumedAll : Slice :=
          { (Slice.ofCell (Cell.mkOrdinary #[true] #[Cell.empty])) with bitPos := 1, refPos := 1 }
        let refs4 : Array Cell := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty]
        let saturated : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        expectOkStack "ok/full-builder-accepts-empty-remaining-slice"
          (runStsliceAltDirect #[.slice consumedAll, .builder saturated])
          #[.builder saturated]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStsliceAltDirect #[.null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty])
          #[.null, .builder Builder.empty] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStsliceAltDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runStsliceAltDirect #[.slice (Slice.ofCell Cell.empty)]) .stkUnd
        expectErr "underflow/one-builder"
          (runStsliceAltDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStsliceAltDirect #[.slice (Slice.ofCell Cell.empty), .null]) .typeChk
        expectErr "type/second-not-slice"
          (runStsliceAltDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-args-builder-below-slice-top"
          (runStsliceAltDirect #[.builder Builder.empty, .slice (Slice.ofCell Cell.empty)]) .typeChk
        expectErr "type/both-wrong-top-first"
          (runStsliceAltDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/cellov-bits-and-refs"
      run := do
        let srcBit1 : Slice := Slice.ofCell (Cell.ofUInt 1 1)
        expectErr "cellov/bits-target-1023-src-1"
          (runStsliceAltDirect #[.slice srcBit1, .builder fullBuilder1023]) .cellOv

        let refs4 : Array Cell := #[Cell.empty, Cell.empty, Cell.empty, Cell.empty]
        let bRef4 : Builder := { bits := #[], refs := refs4 }
        let srcRef1 : Slice := Slice.ofCell (Cell.mkOrdinary #[] #[Cell.empty])
        expectErr "cellov/refs-target-4-src-ref-1"
          (runStsliceAltDirect #[.slice srcRef1, .builder bRef4]) .cellOv

        let bFullRef4 : Builder := { bits := fullBuilder1023.bits, refs := refs4 }
        let srcBoth : Slice := Slice.ofCell (Cell.mkOrdinary #[true] #[Cell.empty])
        expectErr "cellov/bits-and-refs-target-saturated"
          (runStsliceAltDirect #[.slice srcBoth, .builder bFullRef4]) .cellOv }
    ,
    { name := "unit/opcode/alt-decode-and-canonical-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [stsliceInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits stsliceCanonicalOpcode 8 then
          pure ()
        else
          throw (IO.userError s!"stslice canonical encode mismatch: got bits {canonicalOnly.bits}")

        let aliasSlice := mkSliceFromBits (natToBits stsliceAltAliasOpcode 16)
        let _ ← expectDecodeStep "decode/alt-cf12-to-stslice" aliasSlice stsliceInstr 16

        let canonicalProgram : Array Instr := #[stsliceInstr, .add]
        let canonicalCode ←
          match assembleCp0 canonicalProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical sequence failed: {e}")
        let s0 := Slice.ofCell canonicalCode
        let s1 ← expectDecodeStep "decode/canonical-ce" s0 stsliceInstr 8
        let s2 ← expectDecodeStep "decode/canonical-tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/canonical-end: expected exhausted slice, got {s2.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let aliasCode : Cell :=
          Cell.mkOrdinary
            (natToBits stsliceAltAliasOpcode 16 ++ natToBits stsliceCanonicalOpcode 8 ++ addCell.bits)
            #[]
        let a0 := Slice.ofCell aliasCode
        let a1 ← expectDecodeStep "decode/alias-cf12" a0 stsliceInstr 16
        let a2 ← expectDecodeStep "decode/alias-followed-by-canonical-ce" a1 stsliceInstr 8
        let a3 ← expectDecodeStep "decode/alias-tail-add" a2 .add 8
        if a3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/alias-end: expected exhausted slice, got {a3.bitsRemaining} bits remaining")

        let decodedAliasInstr ←
          match decodeCp0WithBits aliasSlice with
          | .ok (instr, _, _) => pure instr
          | .error e => throw (IO.userError s!"decode alias for direct-exec failed: {e}")
        let aliasSourceCell : Cell := Cell.mkOrdinary (natToBits 5 3) #[Cell.empty]
        let aliasSourceSlice := Slice.ofCell aliasSourceCell
        let aliasTargetBuilder : Builder := { bits := natToBits 3 2, refs := #[Cell.empty] }
        let aliasExpected : Builder :=
          { bits := aliasTargetBuilder.bits ++ aliasSourceCell.bits
            refs := aliasTargetBuilder.refs ++ aliasSourceCell.refs }
        expectOkStack "alias-decoded-exec-equals-stslice"
          (runHandlerDirect execInstrCellStSlice decodedAliasInstr
            #[.slice aliasSourceSlice, .builder aliasTargetBuilder])
          #[.builder aliasExpected] }
    ,
    { name := "unit/dispatch/non-stslice-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStsliceAltDispatchFallback #[.null])
          #[.null, intV 53010] }
  ]
  oracle := #[
    mkStsliceAltCase "ok/empty-slice-empty-builder"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty],
    mkStsliceAltCase "ok/deep-stack-preserve-below"
      #[.null, .slice (Slice.ofCell Cell.empty), .builder Builder.empty],

    mkStsliceAltProgramCase "ok/program/src0r0-dst0r0" #[] (mkStsliceProgram 0 0 0 0),
    mkStsliceAltProgramCase "ok/program/src1r0-dst0r0" #[] (mkStsliceProgram 1 0 0 0 (.num 1)),
    mkStsliceAltProgramCase "ok/program/src8r0-dst3r0" #[] (mkStsliceProgram 8 0 3 0 (.num 170) (.num 5)),
    mkStsliceAltProgramCase "ok/program/src15r0-dst7r0" #[] (mkStsliceProgram 15 0 7 0 (.num 177) (.num 91)),
    mkStsliceAltProgramCase "ok/program/src0r1-dst0r0" #[] (mkStsliceProgram 0 1 0 0),
    mkStsliceAltProgramCase "ok/program/src4r1-dst2r2" #[] stsliceAltAppendProgram,
    mkStsliceAltProgramCase "ok/program/src4r2-dst7r1" #[] stsliceAltAppendWithRefsProgram,
    mkStsliceAltProgramCase "ok/program/src2r2-dst5r1" #[] (mkStsliceProgram 2 2 5 1 (.num 2) (.num 3)),
    mkStsliceAltProgramCase "ok/program/refs-boundary-src1-dst3" #[] stsliceAltRefsBoundarySuccessProgram,
    mkStsliceAltProgramCase "ok/program/bits-boundary-src1-dst1022" #[] stsliceAltBitsBoundarySuccessProgram,
    mkStsliceAltProgramCase "ok/program/full-bits-dst1023-with-empty-src" #[] (mkStsliceProgram 0 0 1023 0),
    mkStsliceAltProgramCase "ok/program/full-refs-dst4-with-empty-src" #[] (mkStsliceProgram 0 0 0 4),
    mkStsliceAltProgramCase "ok/program/noise-below-preserved" #[] (#[.pushNull] ++ mkStsliceProgram 6 1 2 1 (.num 41) (.num 3)),

    mkStsliceAltCase "underflow/empty" #[],
    mkStsliceAltCase "underflow/one-slice" #[.slice (Slice.ofCell Cell.empty)],
    mkStsliceAltCase "underflow/one-builder" #[.builder Builder.empty],
    mkStsliceAltCase "type/top-not-builder" #[.slice (Slice.ofCell Cell.empty), .null],
    mkStsliceAltCase "type/second-not-slice" #[.null, .builder Builder.empty],
    mkStsliceAltCase "type/both-wrong-top-first" #[intV 1, .null],

    mkStsliceAltCase "gas/exact-cost-succeeds"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
      #[.pushInt (.num stsliceAltSetGasExact), .tonEnvOp .setGasLimit, stsliceInstr],
    mkStsliceAltCase "gas/exact-minus-one-out-of-gas"
      #[.slice (Slice.ofCell Cell.empty), .builder Builder.empty]
      #[.pushInt (.num stsliceAltSetGasExactMinusOne), .tonEnvOp .setGasLimit, stsliceInstr],

    mkStsliceAltProgramCase "cellov/program/bits-target1023-src1" #[] stsliceAltCellOvBitsProgram,
    mkStsliceAltProgramCase "cellov/program/bits-target1023-src8" #[] (mkStsliceProgram 8 0 1023 0 (.num 255)),
    mkStsliceAltProgramCase "cellov/program/refs-target4-src1" #[] stsliceAltCellOvRefsProgram,
    mkStsliceAltProgramCase "cellov/program/refs-target4-src2" #[] (mkStsliceProgram 0 2 0 4),
    mkStsliceAltProgramCase "cellov/program/bits-and-refs-target-saturated" #[] stsliceAltCellOvBothProgram,
    mkStsliceAltProgramCase "cellov/program/noise-below-refs-overflow" #[] (#[.pushNull] ++ stsliceAltCellOvRefsProgram)
  ]
  fuzz := #[
    { seed := 2026021101
      count := 500
      gen := genStsliceAltFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSLICE_ALT
