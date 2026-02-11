import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SCUTLAST

/-
SCUTLAST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.scutlast` branch)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xd732`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `.cellOp .scutlast`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_op_args2(..., "SCUTLAST", 1023, 4, ... only_last(bits, refs))`).

Branch map used for this suite:
- dispatch split: `.cellOp .scutlast` handled, non-target ops/instrs fall through to `next`;
- pop order and error ordering: `checkUnderflow 3` -> `refs popNatUpTo 4` -> `bits popNatUpTo 1023` -> `popSlice`;
- success vs failure: suffix extraction from the remaining slice cursor vs `.cellUnd`;
- opcode boundaries: `SCUTLAST=0xd732` between `SSKIPFIRST=0xd731` and `SSKIPLAST=0xd733`.
-/

private def scutlastId : InstrId := { name := "SCUTLAST" }

private def scutlastInstr : Instr := .cellOp .scutlast

private def dispatchSentinel : Int := 9132

private def sdskiplastOpcode : Nat := 0xd723
private def scutfirstOpcode : Nat := 0xd730
private def sskipfirstOpcode : Nat := 0xd731
private def scutlastOpcode : Nat := 0xd732
private def sskiplastOpcode : Nat := 0xd733
private def subsliceOpcode : Nat := 0xd734

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 6 3) #[]

private def refUniverse : Array Cell := #[refLeafA, refLeafB, refLeafC, refLeafD]

private def pickRefs (n : Nat) : Array Cell :=
  refUniverse.extract 0 n

private def mkPatternSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsRefs (stripeBits bits phase) (pickRefs refs)

private def mkScutlastStack (s : Slice) (bits : Int) (refs : Int) (below : Array Value := #[]) : Array Value :=
  below ++ #[.slice s, intV bits, intV refs]

private def mkScutlastStackNat (s : Slice) (bits : Nat) (refs : Nat) (below : Array Value := #[]) : Array Value :=
  mkScutlastStack s (Int.ofNat bits) (Int.ofNat refs) below

private def scutlastExpectedSlice (s : Slice) (bits refs : Nat) : Slice :=
  let dropBits : Nat := s.bitsRemaining - bits
  let dropRefs : Nat := s.refsRemaining - refs
  let fromBits := s.bitPos + dropBits
  let fromRefs := s.refPos + dropRefs
  Slice.ofCell
    (Cell.mkOrdinary
      (s.cell.bits.extract fromBits s.cell.bits.size)
      (s.cell.refs.extract fromRefs s.cell.refs.size))

private def execInstrCellOpScutlastOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .scutlast => execCellOpExt .scutlast next
  | _ => next

private def runScutlastDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpScutlastOnly scutlastInstr stack

private def runScutlastDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellOpScutlastOnly
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def popNatUpToModel (max : Nat) (stack : Array Value) :
    Except Excno (Nat × Array Value) := do
  if h : 0 < stack.size then
    let top := stack.back (h := h)
    let rest := stack.pop
    match top with
    | .int .nan => throw .rangeChk
    | .int (.num n) =>
        if n < 0 then
          throw .rangeChk
        else
          let u := n.toNat
          if u > max then
            throw .rangeChk
          else
            pure (u, rest)
    | _ => throw .typeChk
  else
    throw .stkUnd

private def popSliceModel (stack : Array Value) : Except Excno (Slice × Array Value) := do
  if h : 0 < stack.size then
    let top := stack.back (h := h)
    let rest := stack.pop
    match top with
    | .slice s => pure (s, rest)
    | _ => throw .typeChk
  else
    throw .stkUnd

private def runScutlastModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 3 then
    throw .stkUnd
  let (refs, afterRefs) ← popNatUpToModel 4 stack
  let (bits, afterBits) ← popNatUpToModel 1023 afterRefs
  let (s, below) ← popSliceModel afterBits
  if bits ≤ s.bitsRemaining && refs ≤ s.refsRemaining then
    pure (below.push (.slice (scutlastExpectedSlice s bits refs)))
  else
    throw .cellUnd

private def mkScutlastCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[scutlastInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := scutlastId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def scutlastSetGasExact : Int :=
  computeExactGasBudget scutlastInstr

private def scutlastSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne scutlastInstr

private def scutlastBitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 767, 1023]

private def scutlastRefsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 4]

private def pickScutlastBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (scutlastBitsBoundaryPool.size - 1)
  (scutlastBitsBoundaryPool[idx]!, rng')

private def pickScutlastBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickScutlastBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickScutlastRefsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (scutlastRefsBoundaryPool.size - 1)
  (scutlastRefsBoundaryPool[idx]!, rng')

private def pickScutlastRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickScutlastRefsBoundary rng1
  else
    randNat rng1 0 4

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else .cell Cell.empty
  (v, rng1)

private def genScutlastFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (srcBits0, rng2) := pickScutlastBitsMixed rng1
  let (srcRefs0, rng3) := pickScutlastRefsMixed rng2
  let (phase, rng4) := randNat rng3 0 1
  let source0 := mkPatternSlice srcBits0 srcRefs0 phase
  if shape = 0 then
    let (bits, rng5) := randNat rng4 0 srcBits0
    let (refs, rng6) := randNat rng5 0 srcRefs0
    (mkScutlastCase
      s!"fuzz/ok/mixed/sb-{srcBits0}/sr-{srcRefs0}/b-{bits}/r-{refs}"
      (mkScutlastStackNat source0 bits refs), rng6)
  else if shape = 1 then
    (mkScutlastCase
      s!"fuzz/ok/exact/sb-{srcBits0}/sr-{srcRefs0}"
      (mkScutlastStackNat source0 srcBits0 srcRefs0), rng4)
  else if shape = 2 then
    let (bits, rng5) := randNat rng4 0 srcBits0
    let (refs, rng6) := randNat rng5 0 srcRefs0
    let (noise, rng7) := pickNoise rng6
    (mkScutlastCase
      s!"fuzz/ok/deep/sb-{srcBits0}/sr-{srcRefs0}/b-{bits}/r-{refs}"
      (mkScutlastStackNat source0 bits refs #[noise]), rng7)
  else if shape = 3 then
    let source := mkPatternSlice 1023 4 phase
    let (bits, rng5) := randNat rng4 0 1023
    let (refs, rng6) := randNat rng5 0 4
    (mkScutlastCase
      s!"fuzz/ok/max-source/b-{bits}/r-{refs}"
      (mkScutlastStackNat source bits refs), rng6)
  else if shape = 4 then
    let srcBits := if srcBits0 = 1023 then 1022 else srcBits0
    let source := mkPatternSlice srcBits srcRefs0 phase
    let maxDelta : Nat := Nat.min 8 (1023 - srcBits)
    let (delta, rng5) := randNat rng4 1 maxDelta
    let bits := srcBits + delta
    let (refs, rng6) := randNat rng5 0 srcRefs0
    (mkScutlastCase
      s!"fuzz/cellund/bits-over/sb-{srcBits}/sr-{srcRefs0}/b-{bits}/r-{refs}"
      (mkScutlastStackNat source bits refs), rng6)
  else if shape = 5 then
    let srcRefs := if srcRefs0 = 4 then 3 else srcRefs0
    let source := mkPatternSlice srcBits0 srcRefs phase
    let (refs, rng5) := randNat rng4 (srcRefs + 1) 4
    let (bits, rng6) := randNat rng5 0 srcBits0
    (mkScutlastCase
      s!"fuzz/cellund/refs-over/sb-{srcBits0}/sr-{srcRefs}/b-{bits}/r-{refs}"
      (mkScutlastStackNat source bits refs), rng6)
  else if shape = 6 then
    let srcBits := if srcBits0 = 1023 then 1022 else srcBits0
    let srcRefs := if srcRefs0 = 4 then 3 else srcRefs0
    let source := mkPatternSlice srcBits srcRefs phase
    let maxDelta : Nat := Nat.min 8 (1023 - srcBits)
    let (delta, rng5) := randNat rng4 1 maxDelta
    let bits := srcBits + delta
    let (refs, rng6) := randNat rng5 (srcRefs + 1) 4
    (mkScutlastCase
      s!"fuzz/cellund/both-over/sb-{srcBits}/sr-{srcRefs}/b-{bits}/r-{refs}"
      (mkScutlastStackNat source bits refs), rng6)
  else if shape = 7 then
    (mkScutlastCase "fuzz/underflow/empty" #[], rng4)
  else if shape = 8 then
    (mkScutlastCase "fuzz/underflow/two-items"
      #[.slice source0, intV (Int.ofNat srcBits0)], rng4)
  else if shape = 9 then
    (mkScutlastCase "fuzz/type/refs-not-int"
      #[.slice source0, intV 0, .null], rng4)
  else if shape = 10 then
    (mkScutlastCase "fuzz/range/refs-over4"
      #[.slice source0, intV 0, intV 5], rng4)
  else if shape = 11 then
    (mkScutlastCase "fuzz/type/bits-not-int"
      #[.slice source0, .null, intV 0], rng4)
  else if shape = 12 then
    (mkScutlastCase "fuzz/range/bits-over1023"
      #[.slice source0, intV 1024, intV 0], rng4)
  else if shape = 13 then
    (mkScutlastCase "fuzz/type/slice-not-slice"
      #[.null, intV 0, intV 0], rng4)
  else if shape = 14 then
    (mkScutlastCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice 32 2 1), intV 8, intV 1]
      #[.pushInt (.num scutlastSetGasExact), .tonEnvOp .setGasLimit, scutlastInstr], rng4)
  else
    (mkScutlastCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice 32 2 1), intV 8, intV 1]
      #[.pushInt (.num scutlastSetGasExactMinusOne), .tonEnvOp .setGasLimit, scutlastInstr], rng4)

def suite : InstrSuite where
  id := { name := "SCUTLAST" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-stack-shape"
      run := do
        let checks : Array (String × Slice × Nat × Nat) :=
          #[
            ("ok/empty-source-b0-r0", mkPatternSlice 0 0, 0, 0),
            ("ok/nonempty-source-b0-r0", mkPatternSlice 16 3 1, 0, 0),
            ("ok/bits-only-b5-r0", mkPatternSlice 16 2 0, 5, 0),
            ("ok/refs-only-b0-r2", mkPatternSlice 12 4 1, 0, 2),
            ("ok/mixed-b7-r3", mkPatternSlice 20 4 0, 7, 3),
            ("ok/full-remaining-b32-r4", mkPatternSlice 32 4 1, 32, 4),
            ("ok/max-b1023-r4", mkPatternSlice 1023 4 0, 1023, 4)
          ]
        for (label, s, bits, refs) in checks do
          expectOkStack label
            (runScutlastDirect (mkScutlastStackNat s bits refs))
            #[.slice (scutlastExpectedSlice s bits refs)]

        let deepSlice := mkPatternSlice 18 3 1
        expectOkStack "ok/deep-stack-preserved"
          (runScutlastDirect (mkScutlastStackNat deepSlice 9 2 #[.null, intV 77]))
          #[.null, intV 77, .slice (scutlastExpectedSlice deepSlice 9 2)] }
    ,
    { name := "unit/direct/partial-cursor-takes-tail-of-remaining-window"
      run := do
        let baseCell : Cell := Cell.mkOrdinary (stripeBits 24 0) (pickRefs 4)
        let partialA : Slice := { cell := baseCell, bitPos := 5, refPos := 1 }
        let partialB : Slice := { cell := baseCell, bitPos := 23, refPos := 3 }

        expectOkStack "ok/partial-a/b7-r2"
          (runScutlastDirect (mkScutlastStackNat partialA 7 2))
          #[.slice (scutlastExpectedSlice partialA 7 2)]

        expectOkStack "ok/partial-a/b0-r0"
          (runScutlastDirect (mkScutlastStackNat partialA 0 0))
          #[.slice (scutlastExpectedSlice partialA 0 0)]

        expectOkStack "ok/partial-b/b1-r1"
          (runScutlastDirect (mkScutlastStackNat partialB 1 1))
          #[.slice (scutlastExpectedSlice partialB 1 1)] }
    ,
    { name := "unit/direct/cellund-when-request-exceeds-remaining"
      run := do
        let srcA := mkPatternSlice 7 1
        let srcB := mkPatternSlice 3 0
        expectErr "cellund/bits-over-by1"
          (runScutlastDirect (mkScutlastStackNat srcA 8 1)) .cellUnd
        expectErr "cellund/refs-over-by1"
          (runScutlastDirect (mkScutlastStackNat srcA 7 2)) .cellUnd
        expectErr "cellund/both-over"
          (runScutlastDirect (mkScutlastStackNat srcB 4 1)) .cellUnd

        let baseCell : Cell := Cell.mkOrdinary (stripeBits 24 1) (pickRefs 4)
        let partialSlice : Slice := { cell := baseCell, bitPos := 6, refPos := 2 }
        expectErr "cellund/partial-bits-over"
          (runScutlastDirect (mkScutlastStackNat partialSlice 19 1)) .cellUnd
        expectErr "cellund/partial-refs-over"
          (runScutlastDirect (mkScutlastStackNat partialSlice 5 3)) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-ordering"
      run := do
        let src := mkPatternSlice 12 2
        expectErr "underflow/empty"
          (runScutlastDirect #[]) .stkUnd
        expectErr "underflow/one-item"
          (runScutlastDirect #[.slice src]) .stkUnd
        expectErr "underflow/two-items"
          (runScutlastDirect #[.slice src, intV 1]) .stkUnd

        expectErr "type/refs-not-int"
          (runScutlastDirect #[.slice src, intV 1, .null]) .typeChk
        expectErr "range/refs-nan"
          (runScutlastDirect #[.slice src, intV 1, .int .nan]) .rangeChk
        expectErr "range/refs-negative"
          (runScutlastDirect #[.slice src, intV 1, intV (-1)]) .rangeChk
        expectErr "range/refs-over4"
          (runScutlastDirect #[.slice src, intV 1, intV 5]) .rangeChk
        expectErr "order/refs-before-bits-and-slice"
          (runScutlastDirect #[.null, .null, intV 5]) .rangeChk

        expectErr "type/bits-not-int"
          (runScutlastDirect #[.slice src, .null, intV 1]) .typeChk
        expectErr "range/bits-nan"
          (runScutlastDirect #[.slice src, .int .nan, intV 1]) .rangeChk
        expectErr "range/bits-negative"
          (runScutlastDirect #[.slice src, intV (-1), intV 1]) .rangeChk
        expectErr "range/bits-over1023"
          (runScutlastDirect #[.slice src, intV 1024, intV 1]) .rangeChk
        expectErr "order/bits-before-slice-type"
          (runScutlastDirect #[.null, intV 1024, intV 0]) .rangeChk

        expectErr "type/slice-not-slice"
          (runScutlastDirect #[.null, intV 0, intV 0]) .typeChk }
    ,
    { name := "unit/model/alignment-representative-stacks"
      run := do
        let baseCell : Cell := Cell.mkOrdinary (stripeBits 24 0) (pickRefs 4)
        let partialSlice : Slice := { cell := baseCell, bitPos := 5, refPos := 1 }
        let samples : Array (String × Array Value) :=
          #[
            ("ok/zero-zero", mkScutlastStackNat (mkPatternSlice 16 3 0) 0 0),
            ("ok/mixed", mkScutlastStackNat (mkPatternSlice 20 4 1) 7 3),
            ("ok/deep", mkScutlastStackNat (mkPatternSlice 15 2 1) 5 1 #[.null, intV 9]),
            ("ok/partial", mkScutlastStackNat partialSlice 4 2),
            ("err/cellund-bits", mkScutlastStackNat (mkPatternSlice 3 1 0) 4 1),
            ("err/cellund-refs", mkScutlastStackNat (mkPatternSlice 3 1 1) 3 2),
            ("err/underflow", #[]),
            ("err/type-refs", #[.slice (mkPatternSlice 8 1 0), intV 3, .null]),
            ("err/range-bits", #[.slice (mkPatternSlice 8 1 1), intV 1024, intV 0]),
            ("err/type-slice", #[.null, intV 0, intV 0])
          ]
        for (label, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runScutlastDirect stack)
            (runScutlastModel stack) }
    ,
    { name := "unit/opcode/decode-assembler-and-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [scutlastInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/scutlast failed: {e}")
        if assembled.bits = natToBits scutlastOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/scutlast: expected 0xd732, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/scutlast: expected 16 bits, got {assembled.bits.size}")

        let d0 := Slice.ofCell assembled
        let d1 ← expectDecodeStep "decode/assembled-scutlast" d0 scutlastInstr 16
        if d1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/assembled-end: expected exhausted slice, got {d1.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdskiplastOpcode 16 ++
          natToBits scutfirstOpcode 16 ++
          natToBits sskipfirstOpcode 16 ++
          natToBits scutlastOpcode 16 ++
          natToBits sskiplastOpcode 16 ++
          natToBits subsliceOpcode 16 ++
          addCell.bits
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/raw-sdskiplast-left-neighbor" s0 .sdskiplast 16
        let s2 ← expectDecodeStep "decode/raw-scutfirst" s1 (.cellOp .scutfirst) 16
        let s3 ← expectDecodeStep "decode/raw-sskipfirst" s2 (.cellOp .sskipfirst) 16
        let s4 ← expectDecodeStep "decode/raw-scutlast" s3 scutlastInstr 16
        let s5 ← expectDecodeStep "decode/raw-sskiplast" s4 (.cellOp .sskiplast) 16
        let s6 ← expectDecodeStep "decode/raw-subslice-right-neighbor" s5 (.cellOp .subslice) 16
        let s7 ← expectDecodeStep "decode/raw-tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        match decodeCp0WithBits (mkSliceFromBits (natToBits scutlastOpcode 15)) with
        | .error _ => pure ()
        | .ok (instr, used, _) =>
            match instr with
            | .cellOp .scutlast =>
                throw (IO.userError "decode/truncated: unexpectedly decoded SCUTLAST from 15 bits")
            | _ =>
                if used ≤ 15 then
                  pure ()
                else
                  throw (IO.userError s!"decode/truncated: expected <=15 consumed bits, got {used}") }
    ,
    { name := "unit/dispatch/non-scutlast-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runScutlastDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cell-neighbor-sskiplast"
          (runScutlastDispatchFallback (.cellOp .sskiplast) #[.slice (mkPatternSlice 8 1)])
          #[.slice (mkPatternSlice 8 1), intV dispatchSentinel]
        expectOkStack "dispatch/non-cell-sdcutlast"
          (runScutlastDispatchFallback .sdcutlast #[intV 7])
          #[intV 7, intV dispatchSentinel] }
  ]
  oracle := #[
    mkScutlastCase "ok/b0-r0/empty-source"
      (mkScutlastStackNat (mkPatternSlice 0 0) 0 0),
    mkScutlastCase "ok/b0-r0/nonempty-source"
      (mkScutlastStackNat (mkPatternSlice 16 3 1) 0 0),
    mkScutlastCase "ok/b1-r0"
      (mkScutlastStackNat (mkPatternSlice 1 0) 1 0),
    mkScutlastCase "ok/b8-r0"
      (mkScutlastStackNat (mkPatternSlice 32 1 0) 8 0),
    mkScutlastCase "ok/b16-r1"
      (mkScutlastStackNat (mkPatternSlice 24 2 1) 16 1),
    mkScutlastCase "ok/b31-r0"
      (mkScutlastStackNat (mkPatternSlice 63 1 1) 31 0),
    mkScutlastCase "ok/b64-r2"
      (mkScutlastStackNat (mkPatternSlice 96 2 0) 64 2),
    mkScutlastCase "ok/b127-r3"
      (mkScutlastStackNat (mkPatternSlice 190 3 1) 127 3),
    mkScutlastCase "ok/b255-r4"
      (mkScutlastStackNat (mkPatternSlice 300 4 0) 255 4),
    mkScutlastCase "ok/b256-r0"
      (mkScutlastStackNat (mkPatternSlice 300 1 1) 256 0),
    mkScutlastCase "ok/b512-r1"
      (mkScutlastStackNat (mkPatternSlice 700 2 0) 512 1),
    mkScutlastCase "ok/b1023-r4"
      (mkScutlastStackNat (mkPatternSlice 1023 4 1) 1023 4),
    mkScutlastCase "ok/full-source-b20-r2"
      (mkScutlastStackNat (mkPatternSlice 20 2) 20 2),
    mkScutlastCase "ok/refs-only-b0-r2"
      (mkScutlastStackNat (mkPatternSlice 20 3 1) 0 2),
    mkScutlastCase "ok/bits-only-b13-r0"
      (mkScutlastStackNat (mkPatternSlice 20 3 0) 13 0),
    mkScutlastCase "ok/source-b0-r4-cut-r4"
      (mkScutlastStackNat (mkPatternSlice 0 4 1) 0 4),
    mkScutlastCase "ok/deep-stack-one-below"
      (mkScutlastStackNat (mkPatternSlice 18 2 1) 9 1 #[.null]),
    mkScutlastCase "ok/deep-stack-two-below"
      (mkScutlastStackNat (mkPatternSlice 40 4 0) 11 2 #[intV (-5), .null]),

    mkScutlastCase "cellund/bits-over-by1"
      (mkScutlastStackNat (mkPatternSlice 7 1 0) 8 1),
    mkScutlastCase "cellund/refs-over-by1"
      (mkScutlastStackNat (mkPatternSlice 7 1 1) 7 2),
    mkScutlastCase "cellund/both-over"
      (mkScutlastStackNat (mkPatternSlice 3 0 0) 4 1),
    mkScutlastCase "cellund/empty-source-need1bit"
      (mkScutlastStackNat (mkPatternSlice 0 2 1) 1 0),
    mkScutlastCase "cellund/empty-source-need1ref"
      (mkScutlastStackNat (mkPatternSlice 12 0 0) 0 1),
    mkScutlastCase "cellund/short-source-need1023"
      (mkScutlastStackNat (mkPatternSlice 1022 4 1) 1023 4),

    mkScutlastCase "underflow/empty" #[],
    mkScutlastCase "underflow/one-item"
      #[.slice (mkPatternSlice 8 1)],
    mkScutlastCase "underflow/two-items"
      #[.slice (mkPatternSlice 8 1), intV 1],
    mkScutlastCase "type/refs-not-int"
      #[.slice (mkPatternSlice 10 2), intV 3, .null],
    mkScutlastCase "range/refs-negative"
      #[.slice (mkPatternSlice 10 2), intV 3, intV (-1)],
    mkScutlastCase "range/refs-over4"
      #[.slice (mkPatternSlice 10 2), intV 3, intV 5],
    mkScutlastCase "type/bits-not-int"
      #[.slice (mkPatternSlice 10 2), .null, intV 0],
    mkScutlastCase "range/bits-over1023"
      #[.slice (mkPatternSlice 10 2), intV 1024, intV 0],
    mkScutlastCase "type/slice-not-slice"
      #[.null, intV 0, intV 0],

    mkScutlastCase "gas/exact-cost-succeeds"
      #[.slice (mkPatternSlice 32 2 1), intV 8, intV 1]
      #[.pushInt (.num scutlastSetGasExact), .tonEnvOp .setGasLimit, scutlastInstr],
    mkScutlastCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPatternSlice 32 2 1), intV 8, intV 1]
      #[.pushInt (.num scutlastSetGasExactMinusOne), .tonEnvOp .setGasLimit, scutlastInstr]
  ]
  fuzz := #[
    { seed := 2026021104
      count := 280
      gen := genScutlastFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SCUTLAST
