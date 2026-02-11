import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCUTFIRST

/-
SDCUTFIRST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sdcutfirst.lean`
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd720` decode to `.sdcutfirst`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdcutfirst` encode as `0xd720`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_op_args(... "SDCUTFIRST", 1023, only_first(bits))` at `0xd720`).

Branch map used for this suite:
- dispatch guard (`.sdcutfirst` vs fallback);
- `checkUnderflow 2`;
- `popNatUpTo 1023` (type/range split on top value);
- `popSlice` type-check on next stack value;
- `haveBits bits` split: success builds fresh slice (bits only, refs dropped) vs `.cellUnd`;
- opcode/decode boundaries for `0xd720` against nearby `0xd71b`, `0xd721..0xd724`, and `0xd730`.

Oracle serialization caveat:
- oracle/fuzz cases use full-cell slices only; partial cursor slices are covered in unit tests.
-/

private def sdcutfirstId : InstrId := { name := "SDCUTFIRST" }

private def sdcutfirstInstr : Instr := .sdcutfirst
private def sdskipfirstInstr : Instr := .sdskipfirst
private def sdcutlastInstr : Instr := .sdcutlast
private def sdskiplastInstr : Instr := .sdskiplast
private def sdsubstrInstr : Instr := .cellOp .sdSubstr
private def scutfirstInstr : Instr := .cellOp .scutfirst
private def pldslicexqInstr : Instr := .loadSliceX true true

private def sdcutfirstOpcode : Nat := 0xd720
private def dispatchSentinel : Int := 53720

private def mkSdcutfirstCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdcutfirstInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdcutfirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdcutfirstProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdcutfirstId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdcutfirstDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdcutfirst sdcutfirstInstr stack

private def runSdcutfirstDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdcutfirst instr (VM.push (intV dispatchSentinel)) stack

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 13 4) #[]

private def refPool : Array Cell := #[refLeafA, refLeafB, refLeafC, refLeafD]

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def sliceSingleTrue : Slice := mkSliceWithBitsRefs #[true]
private def sliceFive : Slice := mkSliceWithBitsRefs #[true, false, true, false, true]
private def sliceEight : Slice := mkSliceWithBitsRefs #[true, false, true, true, false, true, false, false]
private def sliceRefsOnly : Slice := mkSliceWithBitsRefs #[] #[refLeafA, refLeafB, refLeafC]
private def sliceBitsRefs10 : Slice := mkSliceWithBitsRefs (stripeBits 10 1) #[refLeafA, refLeafB]
private def sliceStripe255 : Slice := mkSliceWithBitsRefs (stripeBits 255 0)
private def sliceStripe512 : Slice := mkSliceWithBitsRefs (stripeBits 512 1)
private def sliceStripe1023 : Slice := mkSliceWithBitsRefs (stripeBits 1023 0)

private def partialCursorCell : Cell :=
  Cell.mkOrdinary
    #[false, true, true, false, true, false, false, true, true, false]
    #[refLeafA, refLeafB, refLeafC]

private def partialSliceBitPos2 : Slice :=
  { cell := partialCursorCell, bitPos := 2, refPos := 0 }

private def partialSliceBitPos4Ref2 : Slice :=
  { cell := partialCursorCell, bitPos := 4, refPos := 2 }

private def partialSliceAtEnd : Slice :=
  { cell := partialCursorCell, bitPos := partialCursorCell.bits.size, refPos := 1 }

private def expectedCutSlice (s : Slice) (bits : Nat) : Slice :=
  let newCell : Cell :=
    Cell.mkOrdinary
      (s.cell.bits.extract s.bitPos (s.bitPos + bits))
      #[]
  Slice.ofCell newCell

private def popNatUpToModel (v : Value) (max : Nat) : Except Excno Nat := do
  match v with
  | .int .nan => throw .rangeChk
  | .int (.num n) =>
      if n < 0 then
        throw .rangeChk
      let u := n.toNat
      if u > max then
        throw .rangeChk
      pure u
  | _ => throw .typeChk

private def runSdcutfirstModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 2 then
    throw .stkUnd
  let bitsV := stack.back!
  let rest := stack.extract 0 (stack.size - 1)
  let bits ← popNatUpToModel bitsV 1023
  let sliceV := rest.back!
  let below := rest.extract 0 (rest.size - 1)
  let s ←
    match sliceV with
    | .slice s => pure s
    | _ => throw .typeChk
  if s.haveBits bits then
    pure (below.push (.slice (expectedCutSlice s bits)))
  else
    throw .cellUnd

private def sdcutfirstSetGasExact : Int :=
  computeExactGasBudget sdcutfirstInstr

private def sdcutfirstSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdcutfirstInstr

private def rangeNanProgram : Array Instr :=
  #[.pushInt .nan, sdcutfirstInstr]

private def sdcutfirstLens : Array Nat :=
  #[0, 1, 2, 3, 5, 8, 15, 31, 63, 127, 255, 511, 1023]

private def pickSdcutfirstLen (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (sdcutfirstLens.size - 1)
  (sdcutfirstLens[idx]!, rng')

private def mkPatternSlice (len refsCount phase : Nat) : Slice :=
  let cappedRefs := Nat.min refsCount refPool.size
  mkSliceWithBitsRefs (stripeBits len phase) (refPool.extract 0 cappedRefs)

private def pickNonIntValue (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 3
  let v : Value :=
    if tag = 0 then .null
    else if tag = 1 then .cell refLeafA
    else if tag = 2 then .builder Builder.empty
    else .tuple #[]
  (v, rng')

private def pickNonSliceValue (rng : StdGen) : Value × StdGen :=
  let (tag, rng') := randNat rng 0 3
  let v : Value :=
    if tag = 0 then .null
    else if tag = 1 then intV 17
    else if tag = 2 then .cell refLeafB
    else .builder Builder.empty
  (v, rng')

private def genSdcutfirstFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (len, rng2) := pickSdcutfirstLen rng1
    let (phase, rng3) := randNat rng2 0 3
    let (refs, rng4) := randNat rng3 0 4
    let s := mkPatternSlice len refs phase
    (mkSdcutfirstCase s!"fuzz/ok/exact/len-{len}/refs-{refs}"
      #[.slice s, intV (Int.ofNat len)], rng4)
  else if shape = 1 then
    let (len, rng2) := randNat rng1 1 1023
    let (bits, rng3) := randNat rng2 0 (len - 1)
    let (phase, rng4) := randNat rng3 0 3
    let s := mkPatternSlice len 2 phase
    (mkSdcutfirstCase s!"fuzz/ok/tail/len-{len}/bits-{bits}"
      #[.slice s, intV (Int.ofNat bits)], rng4)
  else if shape = 2 then
    let (len, rng2) := randNat rng1 0 1023
    let (bits, rng3) := randNat rng2 0 len
    let (phase, rng4) := randNat rng3 0 3
    let s := mkPatternSlice len 1 phase
    let noise : Value := if len % 2 = 0 then .null else intV 41
    (mkSdcutfirstCase s!"fuzz/ok/deep/len-{len}/bits-{bits}"
      #[noise, .slice s, intV (Int.ofNat bits)], rng4)
  else if shape = 3 then
    let (len, rng2) := randNat rng1 0 1022
    let bits := len + 1
    let s := mkPatternSlice len 0 0
    (mkSdcutfirstCase s!"fuzz/cellund/by1/len-{len}"
      #[.slice s, intV (Int.ofNat bits)], rng2)
  else if shape = 4 then
    let (len, rng2) := randNat rng1 0 960
    let (delta, rng3) := randNat rng2 2 63
    let bits := len + delta
    let s := mkPatternSlice len 3 1
    (mkSdcutfirstCase s!"fuzz/cellund/delta-{delta}/len-{len}"
      #[.slice s, intV (Int.ofNat bits)], rng3)
  else if shape = 5 then
    let (n, rng2) := randNat rng1 1 7
    (mkSdcutfirstCase s!"fuzz/range/negative-{n}"
      #[.slice sliceFive, intV (-(Int.ofNat n))], rng2)
  else if shape = 6 then
    let (n, rng2) := randNat rng1 1024 1400
    (mkSdcutfirstCase s!"fuzz/range/overflow-{n}"
      #[.slice sliceFive, intV (Int.ofNat n)], rng2)
  else if shape = 7 then
    let (len, rng2) := randNat rng1 0 64
    let s := mkPatternSlice len 1 0
    (mkSdcutfirstProgramCase s!"fuzz/range/nan/len-{len}"
      #[.slice s] rangeNanProgram, rng2)
  else if shape = 8 then
    (mkSdcutfirstCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 9 then
    let (len, rng2) := randNat rng1 0 64
    let s := mkPatternSlice len 0 2
    (mkSdcutfirstCase s!"fuzz/underflow/one-item-slice/len-{len}" #[.slice s], rng2)
  else if shape = 10 then
    let (bad, rng2) := pickNonIntValue rng1
    (mkSdcutfirstCase "fuzz/type/top-not-int" #[.slice sliceEight, bad], rng2)
  else if shape = 11 then
    let (badSlice, rng2) := pickNonSliceValue rng1
    (mkSdcutfirstCase "fuzz/type/slice-not-slice" #[badSlice, intV 1], rng2)
  else if shape = 12 then
    (mkSdcutfirstCase "fuzz/error-order/range-before-slice-type" #[.null, intV 1300], rng1)
  else
    (mkSdcutfirstCase "fuzz/error-order/bits-type-before-slice-type" #[intV 4, .null], rng1)

def suite : InstrSuite where
  id := { name := "SDCUTFIRST" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-ref-drop"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("ok/bits0-empty", sliceEmpty, 0),
            ("ok/bits0-refs-only", sliceRefsOnly, 0),
            ("ok/bits1-single", sliceSingleTrue, 1),
            ("ok/bits5-exact", sliceFive, 5),
            ("ok/bits5-with-tail", sliceEight, 5),
            ("ok/bits10-refs-ignored", sliceBitsRefs10, 10),
            ("ok/bits255", sliceStripe255, 255),
            ("ok/bits1023", sliceStripe1023, 1023)
          ]
        for (name, s, bits) in checks do
          expectOkStack name
            (runSdcutfirstDirect #[.slice s, intV (Int.ofNat bits)])
            #[.slice (expectedCutSlice s bits)]

        expectOkStack "ok/deep-stack-preserve-below"
          (runSdcutfirstDirect #[.null, intV 77, .slice sliceEight, intV 5])
          #[.null, intV 77, .slice (expectedCutSlice sliceEight 5)] }
    ,
    { name := "unit/direct/partial-cursor-uses-current-bitpos"
      run := do
        expectOkStack "partial/bitpos2-bits3"
          (runSdcutfirstDirect #[.slice partialSliceBitPos2, intV 3])
          #[.slice (expectedCutSlice partialSliceBitPos2 3)]

        expectOkStack "partial/bitpos4-refpos2-bits4"
          (runSdcutfirstDirect #[.slice partialSliceBitPos4Ref2, intV 4])
          #[.slice (expectedCutSlice partialSliceBitPos4Ref2 4)]

        expectOkStack "partial/at-end-bits0"
          (runSdcutfirstDirect #[.slice partialSliceAtEnd, intV 0])
          #[.slice (expectedCutSlice partialSliceAtEnd 0)] }
    ,
    { name := "unit/direct/cellund-on-insufficient-bits"
      run := do
        expectErr "cellund/empty-bits1"
          (runSdcutfirstDirect #[.slice sliceEmpty, intV 1]) .cellUnd
        expectErr "cellund/short-by-one"
          (runSdcutfirstDirect #[.slice sliceFive, intV 6]) .cellUnd
        expectErr "cellund/partial-short"
          (runSdcutfirstDirect #[.slice partialSliceBitPos2, intV 9]) .cellUnd
        expectErr "cellund/at-end-bits1"
          (runSdcutfirstDirect #[.slice partialSliceAtEnd, intV 1]) .cellUnd }
    ,
    { name := "unit/direct/range-errors-and-priority"
      run := do
        expectErr "range/negative"
          (runSdcutfirstDirect #[.slice sliceFive, intV (-1)]) .rangeChk
        expectErr "range/overflow-1024"
          (runSdcutfirstDirect #[.slice sliceFive, intV 1024]) .rangeChk
        expectErr "range/nan"
          (runSdcutfirstDirect #[.slice sliceFive, .int .nan]) .rangeChk
        expectErr "error-order/range-before-slice-type"
          (runSdcutfirstDirect #[.null, intV 1300]) .rangeChk
        expectErr "error-order/range-before-cellund"
          (runSdcutfirstDirect #[.slice sliceEmpty, intV 1024]) .rangeChk }
    ,
    { name := "unit/direct/type-errors-and-order"
      run := do
        expectErr "type/top-null"
          (runSdcutfirstDirect #[.slice sliceFive, .null]) .typeChk
        expectErr "type/top-cell"
          (runSdcutfirstDirect #[.slice sliceFive, .cell refLeafA]) .typeChk
        expectErr "type/top-builder"
          (runSdcutfirstDirect #[.slice sliceFive, .builder Builder.empty]) .typeChk
        expectErr "type/top-empty-tuple"
          (runSdcutfirstDirect #[.slice sliceFive, .tuple #[]]) .typeChk
        expectErr "type/slice-pop-not-slice-int"
          (runSdcutfirstDirect #[intV 9, intV 1]) .typeChk
        expectErr "type/slice-pop-not-slice-null"
          (runSdcutfirstDirect #[.null, intV 0]) .typeChk
        expectErr "error-order/bits-type-before-slice-type"
          (runSdcutfirstDirect #[intV 3, .null]) .typeChk }
    ,
    { name := "unit/direct/underflow"
      run := do
        expectErr "underflow/empty"
          (runSdcutfirstDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runSdcutfirstDirect #[.slice sliceFive]) .stkUnd
        expectErr "underflow/one-item-int"
          (runSdcutfirstDirect #[intV 1]) .stkUnd }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/bits0-empty", #[.slice sliceEmpty, intV 0]),
            ("ok/bits5", #[.slice sliceEight, intV 5]),
            ("ok/refs-ignored", #[.slice sliceBitsRefs10, intV 4]),
            ("ok/partial-cursor", #[.slice partialSliceBitPos4Ref2, intV 4]),
            ("ok/deep-stack", #[.null, intV 11, .slice sliceFive, intV 3]),
            ("err/cellund", #[.slice sliceFive, intV 7]),
            ("err/range", #[.slice sliceFive, intV 2048]),
            ("err/type-top", #[.slice sliceFive, .null]),
            ("err/type-slice", #[.null, intV 0]),
            ("err/underflow", #[.slice sliceFive])
          ]
        for (name, stack) in samples do
          expectSameOutcome s!"model/{name}"
            (runSdcutfirstDirect stack)
            (runSdcutfirstModel stack) }
    ,
    { name := "unit/opcode/decode-family-and-assembler-boundaries"
      run := do
        let canonical ←
          match assembleCp0 [sdcutfirstInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/canonical failed: {e}")
        if canonical.bits = natToBits sdcutfirstOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/canonical: expected opcode 0xd720, got bits {canonical.bits}")

        let program : Array Instr :=
          #[pldslicexqInstr, sdcutfirstInstr, sdskipfirstInstr, sdcutlastInstr, sdskiplastInstr, sdsubstrInstr, scutfirstInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pldslicexq-left-boundary" s0 pldslicexqInstr 16
        let s2 ← expectDecodeStep "decode/sdcutfirst" s1 sdcutfirstInstr 16
        let s3 ← expectDecodeStep "decode/sdskipfirst-neighbor" s2 sdskipfirstInstr 16
        let s4 ← expectDecodeStep "decode/sdcutlast-neighbor" s3 sdcutlastInstr 16
        let s5 ← expectDecodeStep "decode/sdskiplast-neighbor" s4 sdskiplastInstr 16
        let s6 ← expectDecodeStep "decode/sdsubstr-neighbor" s5 sdsubstrInstr 16
        let s7 ← expectDecodeStep "decode/scutfirst-right-boundary" s6 scutfirstInstr 16
        let s8 ← expectDecodeStep "decode/tail-add" s7 .add 8
        if s8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/asm-end: expected exhausted slice, got {s8.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd71b 16
            ++ natToBits 0xd720 16
            ++ natToBits 0xd721 16
            ++ natToBits 0xd722 16
            ++ natToBits 0xd723 16
            ++ natToBits 0xd724 16
            ++ natToBits 0xd730 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-pldslicexq" r0 pldslicexqInstr 16
        let r2 ← expectDecodeStep "decode/raw-sdcutfirst" r1 sdcutfirstInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdskipfirst" r2 sdskipfirstInstr 16
        let r4 ← expectDecodeStep "decode/raw-sdcutlast" r3 sdcutlastInstr 16
        let r5 ← expectDecodeStep "decode/raw-sdskiplast" r4 sdskiplastInstr 16
        let r6 ← expectDecodeStep "decode/raw-sdsubstr" r5 sdsubstrInstr 16
        let r7 ← expectDecodeStep "decode/raw-scutfirst" r6 scutfirstInstr 16
        let r8 ← expectDecodeStep "decode/raw-tail-add" r7 .add 8
        if r8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r8.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdcutfirst-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runSdcutfirstDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdskipfirst"
          (runSdcutfirstDispatchFallback sdskipfirstInstr #[.slice sliceFive, intV 2])
          #[.slice sliceFive, intV 2, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdcutfirstCase "ok/bits0-empty" #[.slice sliceEmpty, intV 0],
    mkSdcutfirstCase "ok/bits0-refs-only" #[.slice sliceRefsOnly, intV 0],
    mkSdcutfirstCase "ok/bits1-single" #[.slice sliceSingleTrue, intV 1],
    mkSdcutfirstCase "ok/bits5-exact" #[.slice sliceFive, intV 5],
    mkSdcutfirstCase "ok/bits5-with-tail" #[.slice sliceEight, intV 5],
    mkSdcutfirstCase "ok/bits255" #[.slice sliceStripe255, intV 255],
    mkSdcutfirstCase "ok/bits512" #[.slice sliceStripe512, intV 512],
    mkSdcutfirstCase "ok/bits1023" #[.slice sliceStripe1023, intV 1023],
    mkSdcutfirstCase "ok/deep-stack-preserve-below"
      #[.null, intV 42, .slice sliceEight, intV 4],
    mkSdcutfirstCase "ok/refs-ignored"
      #[.slice sliceBitsRefs10, intV 7],

    mkSdcutfirstCase "cellund/empty-bits1" #[.slice sliceEmpty, intV 1],
    mkSdcutfirstCase "cellund/short-by-one" #[.slice sliceFive, intV 6],
    mkSdcutfirstCase "range/negative" #[.slice sliceFive, intV (-1)],
    mkSdcutfirstCase "range/overflow-1024" #[.slice sliceFive, intV 1024],
    mkSdcutfirstProgramCase "range/nan-via-program" #[.slice sliceFive] rangeNanProgram,
    mkSdcutfirstCase "type/top-null" #[.slice sliceFive, .null],
    mkSdcutfirstCase "type/top-cell" #[.slice sliceFive, .cell refLeafA],
    mkSdcutfirstCase "type/slice-not-slice-after-bits" #[intV 9, intV 1],
    mkSdcutfirstCase "underflow/empty" #[],
    mkSdcutfirstCase "underflow/one-item-slice" #[.slice sliceFive],
    mkSdcutfirstCase "error-order/range-before-slice-type" #[.null, intV 1300],
    mkSdcutfirstCase "error-order/bits-type-before-slice-type" #[intV 3, .null],

    mkSdcutfirstCase "gas/exact-cost-succeeds"
      #[.slice sliceEight, intV 5]
      #[.pushInt (.num sdcutfirstSetGasExact), .tonEnvOp .setGasLimit, sdcutfirstInstr],
    mkSdcutfirstCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceEight, intV 5]
      #[.pushInt (.num sdcutfirstSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdcutfirstInstr]
  ]
  fuzz := #[
    { seed := 2026021001
      count := 300
      gen := genSdcutfirstFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDCUTFIRST
