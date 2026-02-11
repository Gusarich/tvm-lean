import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDLEXCMP

/-
SDLEXCMP branch-mapping notes (Lean + TVM behavior):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/SdLexCmp.lean` (`.sdLexCmp` execution)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc704` decode)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdLexCmp` encode)

Branch map covered by this suite:
- dispatch fallthrough for non-`.sdLexCmp` instructions;
- pop order + error paths (`s2` then `s1`; `stkUnd` / `typeChk`);
- success outcomes `-1`, `0`, `1` for lexicographic compare on remaining bits only;
- length tie-break when one remaining-bit prefix equals the other;
- decode/assemble boundaries around neighbors (`0xc703`, `0xc704`, `0xc705`, `0xc708`).
-/

private def sdLexCmpId : InstrId := { name := "SDLEXCMP" }

private def sdLexCmpInstr : Instr := .sdLexCmp
private def sdEqInstr : Instr := .sdEq
private def sdPfxInstr : Instr := .sdPfx

private def sdFirstOpcode : Nat := 0xc703
private def sdLexCmpOpcode : Nat := 0xc704
private def sdEqOpcode : Nat := 0xc705
private def sdPfxOpcode : Nat := 0xc708

private def dispatchSentinel : Int := 904

private def mkSdLexCmpCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdLexCmpInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdLexCmpId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdLexCmpDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdLexCmp sdLexCmpInstr stack

private def runSdLexCmpDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdLexCmp instr (VM.push (intV dispatchSentinel)) stack

private def mkWordSlice
    (bits word : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits ++ tail) refs

private def lexCmpBitsModel (b1 b2 : BitString) : Int :=
  let len1 := b1.size
  let len2 := b2.size
  let len := min len1 len2
  let cmp? :=
    (List.range len).foldl
      (fun acc idx =>
        match acc with
        | some v => some v
        | none =>
            let bit1 := b1[idx]!
            let bit2 := b2[idx]!
            if bit1 == bit2 then none else some (if bit1 then 1 else -1))
      none
  match cmp? with
  | some v => v
  | none =>
      if len1 == len2 then 0 else if len1 < len2 then -1 else 1

private def expectedCmp (s1 s2 : Slice) : Int :=
  lexCmpBitsModel (s1.readBits s1.bitsRemaining) (s2.readBits s2.bitsRemaining)

private def expectCmpStack
    (label : String)
    (below : Array Value)
    (s1 s2 : Slice) : IO Unit := do
  let stack := below ++ #[.slice s1, .slice s2]
  let expected := below.push (intV (expectedCmp s1 s2))
  expectOkStack label (runSdLexCmpDirect stack) expected

private def mkPairCase (name : String) (s1 s2 : Slice) : OracleCase :=
  mkSdLexCmpCase name #[.slice s1, .slice s2]

private def mkDeepPairCase (name : String) (below : Array Value) (s1 s2 : Slice) : OracleCase :=
  mkSdLexCmpCase name (below ++ #[.slice s1, .slice s2])

private def partialCellA : Cell :=
  Cell.mkOrdinary (stripeBits 40 0) #[refLeafA, refLeafB]

private def partialCellB : Cell :=
  Cell.mkOrdinary (stripeBits 41 1) #[refLeafC]

private def partialSliceA : Slice :=
  { cell := partialCellA, bitPos := 7, refPos := 0 }

private def partialSliceARefsSkipped : Slice :=
  { cell := partialCellA, bitPos := 7, refPos := partialCellA.refs.size }

private def partialSliceB : Slice :=
  { cell := partialCellA, bitPos := 9, refPos := 1 }

private def partialSliceC : Slice :=
  { cell := partialCellB, bitPos := 5, refPos := 0 }

private def emptyRemainingSlice : Slice :=
  { cell := partialCellB, bitPos := partialCellB.bits.size, refPos := partialCellB.refs.size }

private def sEmpty : Slice := mkSliceWithBitsRefs #[]
private def sWord8A5 : Slice := mkWordSlice 8 0xA5
private def sWord8A6 : Slice := mkWordSlice 8 0xA6
private def sWord8A4 : Slice := mkWordSlice 8 0xA4
private def sWord8AA : Slice := mkWordSlice 8 0xAA
private def sWord8AB : Slice := mkWordSlice 8 0xAB
private def sWord8FF : Slice := mkWordSlice 8 0xFF
private def sWord8FE : Slice := mkWordSlice 8 0xFE
private def sPrefixShort : Slice := mkWordSlice 5 21
private def sPrefixLong : Slice := mkSliceWithBitsRefs (natToBits 21 5 ++ tailBits3)
private def sStripe31Phase0 : Slice := mkSliceWithBitsRefs (stripeBits 31 0)
private def sStripe255Phase0 : Slice := mkSliceWithBitsRefs (stripeBits 255 0)
private def sStripe255Phase1 : Slice := mkSliceWithBitsRefs (stripeBits 255 1)
private def sStripe256Phase0 : Slice := mkSliceWithBitsRefs (stripeBits 256 0)
private def sStripe256Phase1 : Slice := mkSliceWithBitsRefs (stripeBits 256 1)
private def sRefsEqLeft : Slice := mkWordSlice 8 0xA5 #[] #[refLeafA]
private def sRefsEqRight : Slice := mkWordSlice 8 0xA5 #[] #[refLeafB, refLeafC]
private def sRefsLessLeft : Slice := mkWordSlice 6 0x2a #[] #[refLeafA, refLeafB]
private def sRefsLessRight : Slice := mkWordSlice 6 0x2b #[] #[refLeafC]

private def sdLexCmpSetGasExact : Int :=
  computeExactGasBudget sdLexCmpInstr

private def sdLexCmpSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdLexCmpInstr

def suite : InstrSuite where
  id := sdLexCmpId
  unit := #[
    { name := "unit/direct/success-lex-order-and-length-tie-break"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("ok/equal/empty-empty", sEmpty, sEmpty),
            ("ok/equal/word8-a5", sWord8A5, sWord8A5),
            ("ok/equal/stripe31", sStripe31Phase0, sStripe31Phase0),
            ("ok/less/first-bit", mkWordSlice 1 0, mkWordSlice 1 1),
            ("ok/greater/first-bit", mkWordSlice 1 1, mkWordSlice 1 0),
            ("ok/less/middle-bit", mkWordSlice 8 0xA6, mkWordSlice 8 0xAE),
            ("ok/greater/middle-bit", mkWordSlice 8 0xAE, mkWordSlice 8 0xA6),
            ("ok/less/last-bit", sWord8AA, sWord8AB),
            ("ok/greater/last-bit", sWord8AB, sWord8AA),
            ("ok/prefix/shorter", sPrefixShort, sPrefixLong),
            ("ok/prefix/longer", sPrefixLong, sPrefixShort),
            ("ok/prefix/empty-vs-nonempty", sEmpty, mkWordSlice 4 0x5),
            ("ok/prefix/nonempty-vs-empty", mkWordSlice 4 0x5, sEmpty),
            ("ok/boundary/stripe255", sStripe255Phase0, sStripe255Phase1),
            ("ok/boundary/stripe256", sStripe256Phase1, sStripe256Phase0)
          ]
        for (label, s1, s2) in checks do
          expectCmpStack label #[] s1 s2 }
    ,
    { name := "unit/direct/refs-ignored-and-deep-stack-preserved"
      run := do
        expectCmpStack "ok/refs-ignored/equal" #[] sRefsEqLeft sRefsEqRight
        expectCmpStack "ok/refs-ignored/less" #[] sRefsLessLeft sRefsLessRight
        expectCmpStack "ok/refs-ignored/greater" #[] sRefsLessRight sRefsLessLeft

        expectCmpStack "ok/deep-stack/null-cell-preserved"
          #[.null, .cell refLeafA] sWord8FF sWord8FE
        expectCmpStack "ok/deep-stack/mixed-preserved"
          #[intV 7, .cell refLeafB, .null] sWord8A4 sWord8A6 }
    ,
    { name := "unit/direct/partial-slices-compare-only-remaining-bits"
      run := do
        let checks : Array (String × Slice × Slice) :=
          #[
            ("ok/partial/a-vs-b", partialSliceA, partialSliceB),
            ("ok/partial/b-vs-c", partialSliceB, partialSliceC),
            ("ok/partial/c-vs-empty", partialSliceC, emptyRemainingSlice),
            ("ok/partial/equal-ignores-refs", partialSliceA, partialSliceARefsSkipped)
          ]
        for (label, s1, s2) in checks do
          expectCmpStack label #[.null] s1 s2 }
    ,
    { name := "unit/direct/underflow-type-and-pop-order"
      run := do
        expectErr "underflow/empty"
          (runSdLexCmpDirect #[]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdLexCmpDirect #[.slice sWord8A5]) .stkUnd

        expectErr "type/top-null"
          (runSdLexCmpDirect #[.slice sWord8A5, .null]) .typeChk
        expectErr "type/top-int"
          (runSdLexCmpDirect #[.slice sWord8A5, intV 1]) .typeChk
        expectErr "type/top-cell"
          (runSdLexCmpDirect #[.slice sWord8A5, .cell refLeafA]) .typeChk
        expectErr "type/top-builder"
          (runSdLexCmpDirect #[.slice sWord8A5, .builder Builder.empty]) .typeChk

        expectErr "type/second-not-slice"
          (runSdLexCmpDirect #[.null, .slice sWord8A5]) .typeChk
        expectErr "type/second-cell"
          (runSdLexCmpDirect #[.cell refLeafA, .slice sWord8A5]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let program : Array Instr := #[.cellOp .sdFirst, sdLexCmpInstr, sdEqInstr, sdPfxInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/neighbor-sdfirst" s0 (.cellOp .sdFirst) 16
        let s2 ← expectDecodeStep "decode/sdlexcmp" s1 sdLexCmpInstr 16
        let s3 ← expectDecodeStep "decode/neighbor-sdeq" s2 sdEqInstr 16
        let s4 ← expectDecodeStep "decode/neighbor-sdpfx" s3 sdPfxInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let asmLexCmp ←
          match assembleCp0 [sdLexCmpInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdlexcmp failed: {e}")
        if asmLexCmp.bits = natToBits sdLexCmpOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdlexcmp: expected 0xc704 word, got bits {asmLexCmp.bits}")
        if asmLexCmp.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdlexcmp: expected 16 bits, got {asmLexCmp.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdFirstOpcode 16
            ++ natToBits sdLexCmpOpcode 16
            ++ natToBits sdEqOpcode 16
            ++ natToBits sdPfxOpcode 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdfirst" r0 (.cellOp .sdFirst) 16
        let r2 ← expectDecodeStep "decode/raw-sdlexcmp" r1 sdLexCmpInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdeq" r2 sdEqInstr 16
        let r4 ← expectDecodeStep "decode/raw-sdpfx" r3 sdPfxInstr 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdlexcmp-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runSdLexCmpDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdeq-neighbor"
          (runSdLexCmpDispatchFallback sdEqInstr #[.slice sWord8A5, .slice sWord8A6])
          #[.slice sWord8A5, .slice sWord8A6, intV dispatchSentinel]
        expectOkStack "dispatch/sdpfx-neighbor"
          (runSdLexCmpDispatchFallback sdPfxInstr #[.slice sWord8A4, .slice sWord8A5])
          #[.slice sWord8A4, .slice sWord8A5, intV dispatchSentinel] }
  ]
  oracle := #[
    mkPairCase "ok/equal/empty-empty" sEmpty sEmpty,
    mkPairCase "ok/equal/word8-a5" sWord8A5 sWord8A5,
    mkPairCase "ok/equal/stripe31" sStripe31Phase0 sStripe31Phase0,
    mkPairCase "ok/equal/refs-ignored" sRefsEqLeft sRefsEqRight,

    mkPairCase "ok/less/first-bit" (mkWordSlice 1 0) (mkWordSlice 1 1),
    mkPairCase "ok/greater/first-bit" (mkWordSlice 1 1) (mkWordSlice 1 0),
    mkPairCase "ok/less/middle-bit" (mkWordSlice 8 0xA6) (mkWordSlice 8 0xAE),
    mkPairCase "ok/greater/middle-bit" (mkWordSlice 8 0xAE) (mkWordSlice 8 0xA6),
    mkPairCase "ok/less/last-bit" sWord8AA sWord8AB,
    mkPairCase "ok/greater/last-bit" sWord8AB sWord8AA,

    mkPairCase "ok/prefix/shorter-negative" sPrefixShort sPrefixLong,
    mkPairCase "ok/prefix/longer-positive" sPrefixLong sPrefixShort,
    mkPairCase "ok/prefix/empty-vs-nonempty" sEmpty (mkWordSlice 4 0x5),
    mkPairCase "ok/prefix/nonempty-vs-empty" (mkWordSlice 4 0x5) sEmpty,

    mkPairCase "ok/boundary/stripe255" sStripe255Phase0 sStripe255Phase1,
    mkPairCase "ok/boundary/stripe256" sStripe256Phase1 sStripe256Phase0,
    mkPairCase "ok/refs-ignored/less" sRefsLessLeft sRefsLessRight,
    mkPairCase "ok/refs-ignored/greater" sRefsLessRight sRefsLessLeft,

    mkDeepPairCase "ok/deep-stack/null-preserved" #[.null] sWord8FF sWord8FE,
    mkDeepPairCase "ok/deep-stack/cell-int-preserved" #[.cell refLeafA, intV 42] sWord8A4 sWord8A6,

    mkSdLexCmpCase "underflow/empty" #[],
    mkSdLexCmpCase "underflow/one-slice" #[.slice sWord8A5],
    mkSdLexCmpCase "type/top-null" #[.slice sWord8A5, .null],
    mkSdLexCmpCase "type/top-int" #[.slice sWord8A5, intV 0],
    mkSdLexCmpCase "type/top-cell" #[.slice sWord8A5, .cell refLeafB],
    mkSdLexCmpCase "type/top-builder" #[.slice sWord8A5, .builder Builder.empty],
    mkSdLexCmpCase "type/second-not-slice" #[.null, .slice sWord8A5],

    mkSdLexCmpCase "gas/exact-cost-succeeds" #[.slice sWord8A5, .slice sWord8A6]
      #[.pushInt (.num sdLexCmpSetGasExact), .tonEnvOp .setGasLimit, sdLexCmpInstr],
    mkSdLexCmpCase "gas/exact-minus-one-out-of-gas" #[.slice sWord8A5, .slice sWord8A6]
      #[.pushInt (.num sdLexCmpSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdLexCmpInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDLEXCMP
