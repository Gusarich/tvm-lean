import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SSKIPLAST

/-
SSKIPLAST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sskiplast`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SSKIPLAST` encode: `0xd733`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd733` decode to `.cellOp .sskiplast`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_op_args2(..., "SSKIPLAST", 1023, 4, skip_last)`).

Branch map used for this suite:
- dispatch guard: only `.cellOp .sskiplast` is handled; others fall through to `next`;
- stack discipline: `checkUnderflow 3` first, then pop order `refs` → `bits` → `slice`;
- range/type ordering: `popNatUpTo 4` for refs before any bits/slice checks, then `popNatUpTo 1023`;
- success branch: keep prefix of remaining slice (`keepBits = remBits - bits`, `keepRefs = remRefs - refs`);
- failure branch: bounds violation (`bits > remBits || refs > remRefs`) raises `cellUnd`;
- opcode/decode boundaries: fixed 16-bit opcode `0xd733` in the `0xd730..0xd734` family.
-/

private def sskiplastId : InstrId := { name := "SSKIPLAST" }

private def sskiplastInstr : Instr := .cellOp .sskiplast
private def scutfirstInstr : Instr := .cellOp .scutfirst
private def sskipfirstInstr : Instr := .cellOp .sskipfirst
private def scutlastInstr : Instr := .cellOp .scutlast
private def subsliceInstr : Instr := .cellOp .subslice

private def sskiplastOpcode : Nat := 0xd733
private def sskiplastGapOpcode : Nat := 0xd735

private def dispatchSentinel : Int := 733

private def execInstrCellOpSskiplastOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sskiplast =>
      execCellOpExt .sskiplast next
  | _ =>
      next

private def mkSskiplastCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sskiplastInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sskiplastId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSskiplastDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSskiplastOnly sskiplastInstr stack

private def runSskiplastDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellOpSskiplastOnly
    instr
    (VM.push (intV dispatchSentinel))
    stack

private def expectDecodeErr
    (label : String)
    (s : Slice)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def mkFullSlice (bits refs : Nat) (phase : Nat := 0) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stripeBits bits phase) (refsByCount refs))

private def expectedSkipLast (s : Slice) (bits refs : Nat) : Slice :=
  let keepBits : Nat := s.bitsRemaining - bits
  let keepRefs : Nat := s.refsRemaining - refs
  let newCell : Cell :=
    Cell.mkOrdinary
      (s.cell.bits.extract s.bitPos (s.bitPos + keepBits))
      (s.cell.refs.extract s.refPos (s.refPos + keepRefs))
  Slice.ofCell newCell

private def mkSskiplastStack (s : Slice) (bits refs : Int) (below : Array Value := #[]) :
    Array Value :=
  below ++ #[.slice s, intV bits, intV refs]

private def mkSskiplastStackNat (s : Slice) (bits refs : Nat) (below : Array Value := #[]) :
    Array Value :=
  mkSskiplastStack s (Int.ofNat bits) (Int.ofNat refs) below

private def expectSkipOk
    (label : String)
    (s : Slice)
    (bits refs : Nat)
    (below : Array Value := #[]) : IO Unit := do
  expectOkStack label
    (runSskiplastDirect (mkSskiplastStackNat s bits refs below))
    (below ++ #[.slice (expectedSkipLast s bits refs)])

private def valueToNatUpTo (v : Value) (max : Nat) : Except Excno Nat := do
  match v with
  | .int .nan => throw .rangeChk
  | .int (.num n) =>
      if n < 0 then
        throw .rangeChk
      let u := n.toNat
      if u > max then
        throw .rangeChk
      pure u
  | _ =>
      throw .typeChk

private def runSskiplastModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 3 then
    throw .stkUnd
  let refsVal := stack.back!
  let st1 := stack.pop
  let refs ← valueToNatUpTo refsVal 4
  let bitsVal := st1.back!
  let st2 := st1.pop
  let bits ← valueToNatUpTo bitsVal 1023
  let sliceVal := st2.back!
  let below := st2.pop
  let s ←
    match sliceVal with
    | .slice s => pure s
    | _ => throw .typeChk
  if bits ≤ s.bitsRemaining && refs ≤ s.refsRemaining then
    pure (below.push (.slice (expectedSkipLast s bits refs)))
  else
    throw .cellUnd

private def sskiplastSetGasExact : Int :=
  computeExactGasBudget sskiplastInstr

private def sskiplastSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sskiplastInstr

private def fuzzBitsPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 255, 511, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    let (idx, rng2) := randNat rng1 0 (fuzzBitsPool.size - 1)
    (fuzzBitsPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    let (idx, rng2) := randNat rng1 0 4
    (idx, rng2)
  else
    randNat rng1 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 91
    else if pick = 2 then .cell refLeafB
    else if pick = 3 then .slice (mkFullSlice 6 0 1)
    else .slice (mkFullSlice 5 1 0)
  (v, rng1)

private def pickFuzzSlice (rng0 : StdGen) : (Slice × Nat × Nat) × StdGen :=
  let (bits, rng1) := pickBitsMixed rng0
  let (refs, rng2) := pickRefsMixed rng1
  let (phase, rng3) := randNat rng2 0 1
  ((mkFullSlice bits refs phase, bits, refs), rng3)

private def genSskiplastFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let ((s, sBits, sRefs), rng2) := pickFuzzSlice rng1
    let (bitsRaw, rng3) := pickBitsMixed rng2
    let (refsRaw, rng4) := pickRefsMixed rng3
    let bits := Nat.min bitsRaw sBits
    let refs := Nat.min refsRaw sRefs
    (mkSskiplastCase s!"fuzz/ok/top/b{sBits}-r{sRefs}/drop-{bits}-{refs}"
      (mkSskiplastStackNat s bits refs), rng4)
  else if shape = 1 then
    let ((s, sBits, sRefs), rng2) := pickFuzzSlice rng1
    let (bitsRaw, rng3) := pickBitsMixed rng2
    let (refsRaw, rng4) := pickRefsMixed rng3
    let bits := Nat.min bitsRaw sBits
    let refs := Nat.min refsRaw sRefs
    let (noise, rng5) := pickNoiseValue rng4
    (mkSskiplastCase s!"fuzz/ok/deep/b{sBits}-r{sRefs}/drop-{bits}-{refs}"
      (mkSskiplastStackNat s bits refs #[noise]), rng5)
  else if shape = 2 then
    let ((s, sBits, sRefs), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase s!"fuzz/ok/drop-all/b{sBits}-r{sRefs}"
      (mkSskiplastStackNat s sBits sRefs), rng2)
  else if shape = 3 then
    let (sBits, rng2) := randNat rng1 0 1022
    let (sRefs, rng3) := pickRefsMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let s := mkFullSlice sBits sRefs phase
    let (bitsOver, rng5) := randNat rng4 (sBits + 1) 1023
    (mkSskiplastCase s!"fuzz/cellund/bits-over/rem-{sBits}/drop-{bitsOver}"
      (mkSskiplastStackNat s bitsOver 0), rng5)
  else if shape = 4 then
    let (sBits, rng2) := pickBitsMixed rng1
    let (sRefs, rng3) := randNat rng2 0 3
    let (phase, rng4) := randNat rng3 0 1
    let s := mkFullSlice sBits sRefs phase
    let (refsOver, rng5) := randNat rng4 (sRefs + 1) 4
    (mkSskiplastCase s!"fuzz/cellund/refs-over/rem-{sRefs}/drop-{refsOver}"
      (mkSskiplastStackNat s 0 refsOver), rng5)
  else if shape = 5 then
    (mkSskiplastCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/underflow/two-items" #[.slice s, intV 0], rng2)
  else if shape = 7 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/type/refs-top-null" #[.slice s, intV 0, .null], rng2)
  else if shape = 8 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/range/refs-too-large" #[.slice s, intV 0, intV 5], rng2)
  else if shape = 9 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/range/refs-negative" #[.slice s, intV 0, intV (-1)], rng2)
  else if shape = 10 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/type/bits-not-int" #[.slice s, .null, intV 0], rng2)
  else if shape = 11 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/range/bits-too-large" #[.slice s, intV 1024, intV 0], rng2)
  else if shape = 12 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/range/bits-negative" #[.slice s, intV (-1), intV 0], rng2)
  else if shape = 13 then
    (mkSskiplastCase "fuzz/type/slice-not-slice" #[.null, intV 0, intV 0], rng1)
  else if shape = 14 then
    let ((s, _, _), rng2) := pickFuzzSlice rng1
    (mkSskiplastCase "fuzz/order/refs-range-before-bits-type" #[.slice s, .null, intV 5], rng2)
  else if shape = 15 then
    (mkSskiplastCase "fuzz/order/bits-range-before-slice-type" #[.null, intV 1024, intV 0], rng1)
  else if shape = 16 then
    let ((s, _, sRefs), rng2) := pickFuzzSlice rng1
    let (refsRaw, rng3) := pickRefsMixed rng2
    let refs := Nat.min refsRaw sRefs
    (mkSskiplastCase "fuzz/range/bits-nan-via-program"
      #[.slice s, intV (Int.ofNat refs)]
      #[.pushInt .nan, .xchg0 1, sskiplastInstr], rng3)
  else if shape = 17 then
    let ((s, sBits, _), rng2) := pickFuzzSlice rng1
    let (bitsRaw, rng3) := pickBitsMixed rng2
    let bits := Nat.min bitsRaw sBits
    (mkSskiplastCase "fuzz/range/refs-nan-via-program"
      #[.slice s, intV (Int.ofNat bits)]
      #[.pushInt .nan, sskiplastInstr], rng3)
  else if shape = 18 then
    let ((s, sBits, sRefs), rng2) := pickFuzzSlice rng1
    let (bitsRaw, rng3) := pickBitsMixed rng2
    let (refsRaw, rng4) := pickRefsMixed rng3
    let bits := Nat.min bitsRaw sBits
    let refs := Nat.min refsRaw sRefs
    (mkSskiplastCase "fuzz/gas/exact"
      (mkSskiplastStackNat s bits refs)
      #[.pushInt (.num sskiplastSetGasExact), .tonEnvOp .setGasLimit, sskiplastInstr], rng4)
  else
    let ((s, sBits, sRefs), rng2) := pickFuzzSlice rng1
    let (bitsRaw, rng3) := pickBitsMixed rng2
    let (refsRaw, rng4) := pickRefsMixed rng3
    let bits := Nat.min bitsRaw sBits
    let refs := Nat.min refsRaw sRefs
    (mkSskiplastCase "fuzz/gas/exact-minus-one"
      (mkSskiplastStackNat s bits refs)
      #[.pushInt (.num sskiplastSetGasExactMinusOne), .tonEnvOp .setGasLimit, sskiplastInstr], rng4)

def suite : InstrSuite where
  id := { name := "SSKIPLAST" }
  unit := #[
    { name := "unit/direct/success-boundaries-and-deep-stack"
      run := do
        let empty := mkFullSlice 0 0
        let sA := mkFullSlice 18 3 0
        let sB := mkFullSlice 9 4 1
        expectSkipOk "ok/empty-noop" empty 0 0
        expectSkipOk "ok/nonempty-noop" sA 0 0
        expectSkipOk "ok/drop-tail-bits" sA 5 0
        expectSkipOk "ok/drop-tail-refs" sA 0 2
        expectSkipOk "ok/drop-tail-both" sA 7 1
        expectSkipOk "ok/drop-all" sA 18 3
        expectSkipOk "ok/drop-only-refs-to-empty" sB 0 4
        expectSkipOk "ok/deep-stack-preserve" sA 6 2 #[.null, intV 42, .cell refLeafD] }
    ,
    { name := "unit/direct/success-partial-cursor"
      run := do
        let baseCell : Cell := Cell.mkOrdinary (stripeBits 24 1) #[refLeafA, refLeafB, refLeafC]
        let partialSlice : Slice := { cell := baseCell, bitPos := 5, refPos := 1 }
        expectSkipOk "ok/partial-noop" partialSlice 0 0
        expectSkipOk "ok/partial-drop-bits" partialSlice 8 0
        expectSkipOk "ok/partial-drop-refs" partialSlice 0 1
        expectSkipOk "ok/partial-drop-both" partialSlice 6 1
        expectSkipOk "ok/partial-drop-all"
          partialSlice partialSlice.bitsRemaining partialSlice.refsRemaining }
    ,
    { name := "unit/direct/errors-underflow"
      run := do
        let s := mkFullSlice 4 1
        expectErr "underflow/empty" (runSskiplastDirect #[]) .stkUnd
        expectErr "underflow/one-item-slice"
          (runSskiplastDirect #[.slice s]) .stkUnd
        expectErr "underflow/one-item-null"
          (runSskiplastDirect #[.null]) .stkUnd
        expectErr "underflow/two-items"
          (runSskiplastDirect #[.slice s, intV 0]) .stkUnd }
    ,
    { name := "unit/direct/errors-type-range-and-order"
      run := do
        let s := mkFullSlice 12 2
        expectErr "type/refs-top-null"
          (runSskiplastDirect #[.slice s, intV 0, .null]) .typeChk
        expectErr "range/refs-too-large"
          (runSskiplastDirect #[.slice s, intV 0, intV 5]) .rangeChk
        expectErr "range/refs-negative"
          (runSskiplastDirect #[.slice s, intV 0, intV (-1)]) .rangeChk
        expectErr "range/refs-nan"
          (runSskiplastDirect #[.slice s, intV 0, .int .nan]) .rangeChk

        expectErr "type/bits-not-int"
          (runSskiplastDirect #[.slice s, .null, intV 0]) .typeChk
        expectErr "range/bits-too-large"
          (runSskiplastDirect #[.slice s, intV 1024, intV 0]) .rangeChk
        expectErr "range/bits-negative"
          (runSskiplastDirect #[.slice s, intV (-1), intV 0]) .rangeChk
        expectErr "range/bits-nan"
          (runSskiplastDirect #[.slice s, .int .nan, intV 0]) .rangeChk

        expectErr "type/slice-not-slice"
          (runSskiplastDirect #[.null, intV 0, intV 0]) .typeChk

        expectErr "order/refs-range-before-bits-type"
          (runSskiplastDirect #[.slice s, .null, intV 5]) .rangeChk
        expectErr "order/refs-type-before-bits-range"
          (runSskiplastDirect #[.slice s, intV 1024, .null]) .typeChk
        expectErr "order/bits-range-before-slice-type"
          (runSskiplastDirect #[.null, intV 1024, intV 0]) .rangeChk
        expectErr "order/bits-type-before-slice-type"
          (runSskiplastDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/direct/errors-cellund"
      run := do
        let s := mkFullSlice 6 2
        expectErr "cellund/bits-over"
          (runSskiplastDirect (mkSskiplastStackNat s 7 0)) .cellUnd
        expectErr "cellund/refs-over"
          (runSskiplastDirect (mkSskiplastStackNat s 0 3)) .cellUnd
        expectErr "cellund/both-over"
          (runSskiplastDirect (mkSskiplastStackNat s 7 3)) .cellUnd

        let partialBase : Cell := Cell.mkOrdinary (stripeBits 17 0) #[refLeafA, refLeafB]
        let partialSlice : Slice := { cell := partialBase, bitPos := 8, refPos := 1 }
        expectErr "cellund/partial-bits-over"
          (runSskiplastDirect (mkSskiplastStackNat partialSlice 10 0)) .cellUnd
        expectErr "cellund/partial-refs-over"
          (runSskiplastDirect (mkSskiplastStackNat partialSlice 0 2)) .cellUnd }
    ,
    { name := "unit/model/alignment-representative"
      run := do
        let sA := mkFullSlice 12 2 0
        let sB := mkFullSlice 0 4 1
        let partialBase : Cell := Cell.mkOrdinary (stripeBits 21 1) #[refLeafA, refLeafB, refLeafC]
        let partialSlice : Slice := { cell := partialBase, bitPos := 3, refPos := 1 }
        let samples : Array (String × Array Value) :=
          #[
            ("ok/noop", mkSskiplastStackNat sA 0 0),
            ("ok/drop-both", mkSskiplastStackNat sA 5 1 #[.null]),
            ("ok/drop-all-refs", mkSskiplastStackNat sB 0 4),
            ("ok/partial", mkSskiplastStackNat partialSlice 7 1),
            ("err/underflow", #[]),
            ("err/type-refs", #[.slice sA, intV 0, .null]),
            ("err/range-bits", #[.slice sA, intV 1024, intV 0]),
            ("err/type-slice", #[.null, intV 0, intV 0]),
            ("err/cellund", mkSskiplastStackNat sA 13 0)
          ]
        for (label, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runSskiplastDirect stack)
            (runSskiplastModel stack) }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-and-gap"
      run := do
        let familyProgram : Array Instr :=
          #[scutfirstInstr, sskipfirstInstr, scutlastInstr, sskiplastInstr, subsliceInstr, .add]
        let familyCode ←
          match assembleCp0 familyProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let s0 := Slice.ofCell familyCode
        let s1 ← expectDecodeStep "decode/scutfirst" s0 scutfirstInstr 16
        let s2 ← expectDecodeStep "decode/sskipfirst" s1 sskipfirstInstr 16
        let s3 ← expectDecodeStep "decode/scutlast" s2 scutlastInstr 16
        let s4 ← expectDecodeStep "decode/sskiplast" s3 sskiplastInstr 16
        let s5 ← expectDecodeStep "decode/subslice" s4 subsliceInstr 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits")

        let singleCode ←
          match assembleCp0 [sskiplastInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sskiplast failed: {e}")
        if singleCode.bits = natToBits sskiplastOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/sskiplast: expected 0x{Nat.toDigits 16 sskiplastOpcode |>.asString}, got {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/sskiplast: expected 16 bits, got {singleCode.bits.size}")

        expectDecodeErr "decode/raw-gap-d735"
          (Slice.ofCell (Cell.mkOrdinary (natToBits sskiplastGapOpcode 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-sskiplast-falls-through"
      run := do
        let s := mkFullSlice 8 2
        let base := mkSskiplastStackNat s 3 1 #[.null]
        expectOkStack "dispatch/add"
          (runSskiplastDispatchFallback .add #[.null, intV 1])
          #[.null, intV 1, intV dispatchSentinel]
        expectOkStack "dispatch/scutlast-neighbor"
          (runSskiplastDispatchFallback scutlastInstr base)
          (base.push (intV dispatchSentinel))
        expectOkStack "dispatch/sskipfirst-neighbor"
          (runSskiplastDispatchFallback sskipfirstInstr base)
          (base.push (intV dispatchSentinel)) }
  ]
  oracle := #[
    mkSskiplastCase "ok/noop-empty"
      (mkSskiplastStackNat (mkFullSlice 0 0 0) 0 0),
    mkSskiplastCase "ok/noop-nonempty"
      (mkSskiplastStackNat (mkFullSlice 18 3 1) 0 0),
    mkSskiplastCase "ok/drop-tail-bits"
      (mkSskiplastStackNat (mkFullSlice 18 3 0) 7 0),
    mkSskiplastCase "ok/drop-tail-refs"
      (mkSskiplastStackNat (mkFullSlice 18 3 1) 0 2),
    mkSskiplastCase "ok/drop-tail-both"
      (mkSskiplastStackNat (mkFullSlice 20 4 0) 9 3),
    mkSskiplastCase "ok/drop-all"
      (mkSskiplastStackNat (mkFullSlice 12 2 1) 12 2),
    mkSskiplastCase "ok/drop-all-refs-only"
      (mkSskiplastStackNat (mkFullSlice 0 4 0) 0 4),
    mkSskiplastCase "ok/deep-stack-preserved"
      (mkSskiplastStackNat (mkFullSlice 9 2 1) 4 1 #[.null, intV 77]),

    mkSskiplastCase "underflow/empty" #[],
    mkSskiplastCase "underflow/one-item"
      #[.slice (mkFullSlice 7 1 0)],
    mkSskiplastCase "underflow/two-items"
      #[.slice (mkFullSlice 7 1 1), intV 0],
    mkSskiplastCase "type/refs-top-not-int"
      #[.slice (mkFullSlice 10 2 0), intV 0, .null],
    mkSskiplastCase "range/refs-too-large"
      #[.slice (mkFullSlice 10 2 1), intV 0, intV 5],
    mkSskiplastCase "type/bits-not-int"
      #[.slice (mkFullSlice 10 2 0), .null, intV 0],
    mkSskiplastCase "range/bits-too-large"
      #[.slice (mkFullSlice 10 2 1), intV 1024, intV 0],
    mkSskiplastCase "type/slice-not-slice"
      #[.null, intV 0, intV 0],
    mkSskiplastCase "cellund/bits-over-remaining"
      (mkSskiplastStackNat (mkFullSlice 6 2 0) 7 0),
    mkSskiplastCase "cellund/refs-over-remaining"
      (mkSskiplastStackNat (mkFullSlice 6 2 1) 0 3),
    mkSskiplastCase "order/refs-range-before-bits-type"
      #[.slice (mkFullSlice 8 2 0), .null, intV 5],
    mkSskiplastCase "order/bits-range-before-slice-type"
      #[.null, intV 1024, intV 0],

    mkSskiplastCase "gas/exact-cost-succeeds"
      (mkSskiplastStackNat (mkFullSlice 11 3 1) 4 1)
      #[.pushInt (.num sskiplastSetGasExact), .tonEnvOp .setGasLimit, sskiplastInstr],
    mkSskiplastCase "gas/exact-minus-one-out-of-gas"
      (mkSskiplastStackNat (mkFullSlice 11 3 1) 4 1)
      #[.pushInt (.num sskiplastSetGasExactMinusOne), .tonEnvOp .setGasLimit, sskiplastInstr]
  ]
  fuzz := #[
    { seed := 2026021001
      count := 320
      gen := genSskiplastFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SSKIPLAST
