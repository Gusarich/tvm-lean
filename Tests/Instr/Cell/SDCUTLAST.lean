import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDCUTLAST

/-
SDCUTLAST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sdcutlast.lean` (`.sdcutlast`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd722` decode to `.sdcutlast`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sdcutlast` encodes to `0xd722`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`SDCUTLAST` via `exec_slice_op_args(..., cs.only_last(bits))`).

Branch map used for this suite:
- dispatch guard: `.sdcutlast` vs fallthrough to `next`;
- stack sequence: `checkUnderflow 2`, then `popNatUpTo 1023` (type/range), then `popSlice` (type);
- success branch: `bits ≤ s.bitsRemaining`, produce last `bits` of current slice window;
- failure branch: `bits > s.bitsRemaining` => `.cellUnd`;
- result normalization: output is `Slice.ofCell` over extracted bits and always drops refs;
- fixed-width opcode/decode boundaries around `0xd722` with neighbors `0xd720`, `0xd721`, `0xd723`, `0xd724`.
-/

private def sdcutlastId : InstrId := { name := "SDCUTLAST" }

private def sdcutfirstInstr : Instr := .sdcutfirst
private def sdskipfirstInstr : Instr := .sdskipfirst
private def sdcutlastInstr : Instr := .sdcutlast
private def sdskiplastInstr : Instr := .sdskiplast
private def sdsubstrInstr : Instr := .cellOp .sdSubstr

private def sdcutfirstOpcode : Nat := 0xd720
private def sdskipfirstOpcode : Nat := 0xd721
private def sdcutlastOpcode : Nat := 0xd722
private def sdskiplastOpcode : Nat := 0xd723
private def sdsubstrOpcode : Nat := 0xd724

private def dispatchSentinel : Int := 8123

private def mkSliceWord (bits word : Nat) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits) refs

private def mkSdcutlastResultSlice (s : Slice) (bits : Nat) : Slice :=
  let drop : Nat := s.bitsRemaining - bits
  let fromPos : Nat := s.bitPos + drop
  Slice.ofCell (Cell.mkOrdinary (s.cell.bits.extract fromPos (fromPos + bits)) #[])

private def runSdcutlastDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdcutlast sdcutlastInstr stack

private def runSdcutlastDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdcutlast instr (VM.push (intV dispatchSentinel)) stack

private def runSdcutlastModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 2 then
    throw .stkUnd
  let bitsV := stack.back!
  let sV := stack[stack.size - 2]!
  let below := stack.extract 0 (stack.size - 2)
  let bits : Nat ←
    match bitsV with
    | .int .nan => throw .rangeChk
    | .int (.num n) =>
        if n < 0 then
          throw .rangeChk
        let u := n.toNat
        if u > 1023 then
          throw .rangeChk
        pure u
    | _ => throw .typeChk
  match sV with
  | .slice s =>
      if bits ≤ s.bitsRemaining then
        pure (below.push (.slice (mkSdcutlastResultSlice s bits)))
      else
        throw .cellUnd
  | _ =>
      throw .typeChk

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

private def mkSdcutlastCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdcutlastInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdcutlastId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def sEmpty : Slice := mkSliceWithBitsRefs #[]
private def s6_110101 : Slice := mkSliceWord 6 0x35
private def s6_101001 : Slice := mkSliceWord 6 0x29
private def s8_ca_refs : Slice := mkSliceWord 8 0xca #[refLeafA, refLeafB]
private def s16Stripe1 : Slice := mkSliceWithBitsRefs (stripeBits 16 1)
private def s255Stripe0 : Slice := mkSliceWithBitsRefs (stripeBits 255 0)
private def s1023Stripe1 : Slice := mkSliceWithBitsRefs (stripeBits 1023 1)

private def partialCell : Cell :=
  Cell.mkOrdinary
    #[true, false, true, true, false, false, true, false, true, false, true, true]
    #[refLeafA, refLeafB, refLeafC]

private def partialBitPos2 : Slice := { cell := partialCell, bitPos := 2, refPos := 1 }
private def partialBitPos5 : Slice := { cell := partialCell, bitPos := 5, refPos := 0 }
private def partialAtEnd : Slice := { cell := partialCell, bitPos := partialCell.bits.size, refPos := 2 }

private def sdcutlastSetGasExact : Int :=
  computeExactGasBudget sdcutlastInstr

private def sdcutlastSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdcutlastInstr

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (((bitsBoundaryPool[idx]?).getD 0), rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def mkFullSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase) (refsByCount refs)

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell refLeafB, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def genSdcutlastFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (wantBits, rng4) := randNat rng3 0 totalBits
    let (phase, rng5) := randNat rng4 0 3
    let s := mkFullSlice totalBits refs phase
    (mkSdcutlastCase s!"fuzz/ok/full/len{totalBits}/keep{wantBits}/refs{refs}"
      #[.slice s, intV (Int.ofNat wantBits)], rng5)
  else if shape = 1 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (wantBits, rng4) := randNat rng3 0 totalBits
    let (phase, rng5) := randNat rng4 0 3
    let (noise, rng6) := pickNoiseValue rng5
    let s := mkFullSlice totalBits refs phase
    (mkSdcutlastCase "fuzz/ok/deep"
      #[noise, .slice s, intV (Int.ofNat wantBits)], rng6)
  else if shape = 2 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (skipBits, rng4) := randNat rng3 0 totalBits
    let remBits := totalBits - skipBits
    let (wantBits, rng5) := randNat rng4 0 remBits
    let (phase, rng6) := randNat rng5 0 3
    let s := mkFullSlice totalBits refs phase
    let stack : Array Value := #[.slice s, intV (Int.ofNat skipBits)]
    let program : Array Instr := #[sdskipfirstInstr, .pushInt (.num wantBits), sdcutlastInstr]
    (mkSdcutlastCase s!"fuzz/ok/cursor/skip{skipBits}/keep{wantBits}" stack program, rng6)
  else if shape = 3 then
    let (totalBits0, rng2) := randNat rng1 0 1022
    let (refs, rng3) := pickRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 3
    let s := mkFullSlice totalBits0 refs phase
    (mkSdcutlastCase s!"fuzz/cellund/len{totalBits0}/keep{totalBits0 + 1}"
      #[.slice s, intV (Int.ofNat (totalBits0 + 1))], rng4)
  else if shape = 4 then
    let (n, rng2) := randNat rng1 0 1
    if n = 0 then
      (mkSdcutlastCase "fuzz/underflow/empty" #[], rng2)
    else
      (mkSdcutlastCase "fuzz/underflow/one" #[.slice s6_110101], rng2)
  else if shape = 5 then
    let (mode, rng2) := randNat rng1 0 2
    let badBits : Value :=
      if mode = 0 then .null
      else if mode = 1 then .slice sEmpty
      else .cell Cell.empty
    (mkSdcutlastCase "fuzz/type/bits" #[.slice s6_110101, badBits], rng2)
  else if shape = 6 then
    let (mode, rng2) := randNat rng1 0 2
    if mode = 2 then
      let stack : Array Value := #[.slice s6_110101]
      let program : Array Instr := #[.pushInt .nan, sdcutlastInstr]
      (mkSdcutlastCase "fuzz/range/bits-nan" stack program, rng2)
    else
      let badBits : Value :=
        if mode = 0 then intV (-1)
        else intV 1024
      (mkSdcutlastCase "fuzz/range/bits" #[.slice s6_110101, badBits], rng2)
  else
    (mkSdcutlastCase "fuzz/type/slice" #[.null, intV 1], rng1)

def suite : InstrSuite where
  id := { name := "SDCUTLAST" }
  unit := #[
    { name := "unit/direct/success-full-window-boundaries"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("empty-keep0", sEmpty, 0),
            ("len6-keep0", s6_110101, 0),
            ("len6-keep1", s6_110101, 1),
            ("len6-keep3", s6_110101, 3),
            ("len6-keep6", s6_110101, 6),
            ("len16-keep8", s16Stripe1, 8),
            ("len255-keep255", s255Stripe0, 255),
            ("len1023-keep1023", s1023Stripe1, 1023)
          ]
        for (label, s, bits) in checks do
          expectOkStack s!"ok/{label}"
            (runSdcutlastDirect #[.slice s, intV (Int.ofNat bits)])
            #[.slice (mkSdcutlastResultSlice s bits)] }
    ,
    { name := "unit/direct/success-partial-window-and-refs-cleared"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("partial-pos2-keep4", partialBitPos2, 4),
            ("partial-pos2-keep10", partialBitPos2, 10),
            ("partial-pos5-keep0", partialBitPos5, 0),
            ("partial-pos5-keep7", partialBitPos5, 7),
            ("partial-at-end-keep0", partialAtEnd, 0),
            ("refs-full-keep5", s8_ca_refs, 5),
            ("refs-full-keep8", s8_ca_refs, 8)
          ]
        for (label, s, bits) in checks do
          expectOkStack s!"ok/{label}"
            (runSdcutlastDirect #[.slice s, intV (Int.ofNat bits)])
            #[.slice (mkSdcutlastResultSlice s bits)] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        expectOkStack "ok/deep-preserve-len4"
          (runSdcutlastDirect #[.null, intV 77, .slice s6_101001, intV 4])
          #[.null, intV 77, .slice (mkSdcutlastResultSlice s6_101001 4)]
        expectOkStack "ok/deep-preserve-len0"
          (runSdcutlastDirect #[.cell refLeafC, .tuple #[], .slice s6_101001, intV 0])
          #[.cell refLeafC, .tuple #[], .slice (mkSdcutlastResultSlice s6_101001 0)] }
    ,
    { name := "unit/direct/errors-underflow-type-range-cellund"
      run := do
        expectErr "underflow/empty"
          (runSdcutlastDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runSdcutlastDirect #[.slice s6_110101]) .stkUnd

        expectErr "type/top-not-int-null"
          (runSdcutlastDirect #[.slice s6_110101, .null]) .typeChk
        expectErr "type/top-not-int-slice"
          (runSdcutlastDirect #[.slice s6_110101, .slice sEmpty]) .typeChk
        expectErr "type/top-not-int-cell"
          (runSdcutlastDirect #[.slice s6_110101, .cell refLeafA]) .typeChk

        expectErr "range/negative"
          (runSdcutlastDirect #[.slice s6_110101, intV (-1)]) .rangeChk
        expectErr "range/over-1023"
          (runSdcutlastDirect #[.slice s6_110101, intV 1024]) .rangeChk
        expectErr "range/nan"
          (runSdcutlastDirect #[.slice s6_110101, .int .nan]) .rangeChk

        expectErr "type/second-not-slice-null"
          (runSdcutlastDirect #[.null, intV 1]) .typeChk
        expectErr "type/second-not-slice-cell"
          (runSdcutlastDirect #[.cell refLeafA, intV 1]) .typeChk

        expectErr "cellund/bits-gt-remaining"
          (runSdcutlastDirect #[.slice s6_110101, intV 7]) .cellUnd
        expectErr "cellund/partial-bits-gt-remaining"
          (runSdcutlastDirect #[.slice partialBitPos5, intV 8]) .cellUnd }
    ,
    { name := "unit/direct/error-order-range-before-slice-pop"
      run := do
        expectErr "order/range-before-type-second-negative"
          (runSdcutlastDirect #[.null, intV (-1)]) .rangeChk
        expectErr "order/range-before-type-second-too-large"
          (runSdcutlastDirect #[.cell refLeafA, intV 4096]) .rangeChk
        expectErr "order/range-before-type-second-nan"
          (runSdcutlastDirect #[.tuple #[], .int .nan]) .rangeChk
        expectErr "order/type-second-after-valid-bits"
          (runSdcutlastDirect #[.tuple #[], intV 3]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-keep0", #[.slice sEmpty, intV 0]),
            ("ok/len6-keep3", #[.slice s6_110101, intV 3]),
            ("ok/partial-keep4", #[.slice partialBitPos2, intV 4]),
            ("ok/deep", #[.null, intV 5, .slice s6_101001, intV 2]),
            ("err/underflow-empty", #[]),
            ("err/type-top", #[.slice s6_110101, .null]),
            ("err/range-neg", #[.slice s6_110101, intV (-1)]),
            ("err/type-second", #[.null, intV 1]),
            ("err/cellund", #[.slice s6_110101, intV 7])
          ]
        for (label, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runSdcutlastDirect stack)
            (runSdcutlastModel stack) }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [sdcutlastInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdcutlast failed: {e}")
        if assembled.bits = natToBits sdcutlastOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdcutlast: expected opcode 0xd722, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/sdcutlast: expected 16 bits, got {assembled.bits.size}")

        let s1 ← expectDecodeStep "decode/assembled-sdcutlast"
          (Slice.ofCell assembled) sdcutlastInstr 16
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/assembled-sdcutlast: expected exhausted slice, got {s1.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdcutfirstOpcode 16 ++
          natToBits sdskipfirstOpcode 16 ++
          natToBits sdcutlastOpcode 16 ++
          natToBits sdskiplastOpcode 16 ++
          natToBits sdsubstrOpcode 16 ++
          addCell.bits
        let d0 := mkSliceFromBits rawBits
        let d1 ← expectDecodeStep "decode/raw-sdcutfirst" d0 sdcutfirstInstr 16
        let d2 ← expectDecodeStep "decode/raw-sdskipfirst" d1 sdskipfirstInstr 16
        let d3 ← expectDecodeStep "decode/raw-sdcutlast" d2 sdcutlastInstr 16
        let d4 ← expectDecodeStep "decode/raw-sdskiplast" d3 sdskiplastInstr 16
        let d5 ← expectDecodeStep "decode/raw-sdsubstr" d4 sdsubstrInstr 16
        let d6 ← expectDecodeStep "decode/raw-tail-add" d5 .add 8
        if d6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/raw-end: expected exhausted slice, got {d6.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits sdcutlastOpcode 15)) with
        | .ok (instr, _, _) =>
            match instr with
            | .sdcutlast =>
                throw (IO.userError "decode/truncated: unexpectedly decoded SDCUTLAST from 15 bits")
            | _ =>
                pure ()
        | .error _ =>
            pure () }
    ,
    { name := "unit/dispatch/non-sdcutlast-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-op-add"
          (runSdcutlastDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdcutfirst"
          (runSdcutlastDispatchFallback .sdcutfirst #[.slice s6_110101, intV 2])
          #[.slice s6_110101, intV 2, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdskiplast"
          (runSdcutlastDispatchFallback .sdskiplast #[.slice s6_110101, intV 2])
          #[.slice s6_110101, intV 2, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdcutlastCase "ok/empty-keep0"
      #[.slice sEmpty, intV 0],
    mkSdcutlastCase "ok/len6-keep0"
      #[.slice s6_110101, intV 0],
    mkSdcutlastCase "ok/len6-keep3"
      #[.slice s6_110101, intV 3],
    mkSdcutlastCase "ok/len6-keep6"
      #[.slice s6_110101, intV 6],
    mkSdcutlastCase "ok/refs-keep5-drop-refs"
      #[.slice s8_ca_refs, intV 5],
    mkSdcutlastCase "ok/len16-keep8"
      #[.slice s16Stripe1, intV 8],
    mkSdcutlastCase "ok/len255-keep255"
      #[.slice s255Stripe0, intV 255],
    mkSdcutlastCase "ok/len1023-keep1023"
      #[.slice s1023Stripe1, intV 1023],
    mkSdcutlastCase "ok/deep-stack-preserve"
      #[.null, intV 42, .slice s6_101001, intV 4],
    mkSdcutlastCase "ok/len8-keep0-drop-refs"
      #[.slice s8_ca_refs, intV 0],
    mkSdcutlastCase "ok/len8-keep8-drop-refs"
      #[.slice s8_ca_refs, intV 8],

    mkSdcutlastCase "underflow/empty" #[],
    mkSdcutlastCase "underflow/one-item"
      #[.slice s6_110101],
    mkSdcutlastCase "type/top-not-int"
      #[.slice s6_110101, .null],
    mkSdcutlastCase "type/top-not-int-slice"
      #[.slice s6_110101, .slice sEmpty],
    mkSdcutlastCase "range/negative"
      #[.slice s6_110101, intV (-1)],
    mkSdcutlastCase "range/over-1023"
      #[.slice s6_110101, intV 1024],
    mkSdcutlastCase "type/second-not-slice"
      #[.null, intV 1],
    mkSdcutlastCase "cellund/bits-gt-remaining"
      #[.slice s6_110101, intV 7],
    mkSdcutlastCase "cellund/empty-keep1"
      #[.slice sEmpty, intV 1],

    mkSdcutlastCase "gas/exact-cost-succeeds"
      #[.slice s6_110101, intV 3]
      #[.pushInt (.num sdcutlastSetGasExact), .tonEnvOp .setGasLimit, sdcutlastInstr],
    mkSdcutlastCase "gas/exact-minus-one-out-of-gas"
      #[.slice s6_110101, intV 3]
      #[.pushInt (.num sdcutlastSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdcutlastInstr]
  ]
  fuzz := #[
    { seed := 2026021112
      count := 500
      gen := genSdcutlastFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDCUTLAST
