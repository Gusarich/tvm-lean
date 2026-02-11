import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDSUBSTR

/-
SDSUBSTR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdSubstr`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd724` decode to `.cellOp .sdSubstr`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.cellOp .sdSubstr` encode as `0xd724`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_slice_op_args2`, `SDSUBSTR`, `skip_first(offs) && only_first(bits)`).

Branch map used for this suite:
- dispatch guard: only `.cellOp .sdSubstr` is handled by the direct runner;
- stack order: `checkUnderflow 3`, then pop `bits`, then `offs`, then `slice`;
- popNat guards (`popNatUpTo 1023`) for type/range on both integer args;
- success split: `haveBits (offs + bits)` extracts `[offs .. offs+bits)` from current cursor;
- output contract: pushes one fresh slice with refs dropped (`refs = #[]`);
- failure split: insufficient remaining bits throws `.cellUnd`;
- opcode/decode boundary: `0xd723` / `0xd724` / `0xd726` / `0xd727` with decode gap at `0xd725`.
-/

private def sdSubstrId : InstrId := { name := "SDSUBSTR" }

private def sdSubstrInstr : Instr := .cellOp .sdSubstr

private def dispatchSentinel : Int := 724

private def sdskiplastWord : Nat := 0xd723
private def sdsubstrWord : Nat := 0xd724
private def sdbeginsxWord : Nat := 0xd726
private def sdbeginsxqWord : Nat := 0xd727

private structure SubstrCheck where
  label : String
  s : Slice
  offs : Nat
  bits : Nat

private def execInstrCellOpSdSubstrOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdSubstr => execCellOpExt .sdSubstr next
  | _ => next

private def mkSdSubstrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdSubstrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdSubstrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdSubstrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdSubstrOnly sdSubstrInstr stack

private def runSdSubstrDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext
    execInstrCellOpSdSubstrOnly
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
      throw (IO.userError s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

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

private def popNatUpToFromValue (v : Value) (max : Nat := 1023) : Except Excno Nat := do
  match v with
  | .int .nan =>
      throw .rangeChk
  | .int (.num n) =>
      if n < 0 then
        throw .rangeChk
      let u := n.toNat
      if u > max then
        throw .rangeChk
      pure u
  | _ =>
      throw .typeChk

private def runSdSubstrModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 3 then
    throw .stkUnd
  let bitsV := stack.back!
  let st1 := stack.pop
  let offsV := st1.back!
  let st2 := st1.pop
  let sliceV := st2.back!
  let below := st2.pop
  let bits ← popNatUpToFromValue bitsV 1023
  let offs ← popNatUpToFromValue offsV 1023
  match sliceV with
  | .slice s =>
      if s.haveBits (offs + bits) then
        pure (below.push (.slice (Slice.ofCell
          (Cell.mkOrdinary (s.cell.bits.extract (s.bitPos + offs) (s.bitPos + offs + bits)) #[]))))
      else
        throw .cellUnd
  | _ =>
      throw .typeChk

private def patternBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun idx =>
    ((idx.1 + phase) % 3 = 1) || ((idx.1 + phase) % 5 = 0)

private def expectedSubstrSlice (s : Slice) (offs bits : Nat) : Slice :=
  let fromPos := s.bitPos + offs
  let toPos := fromPos + bits
  Slice.ofCell (Cell.mkOrdinary (s.cell.bits.extract fromPos toPos) #[])

private def expectedSubstrStack
    (below : Array Value)
    (s : Slice)
    (offs bits : Nat) : Array Value :=
  below ++ #[.slice (expectedSubstrSlice s offs bits)]

private def bits8A : BitString := natToBits 0xd3 8
private def bits16A : BitString := natToBits 0xabcd 16
private def bits32A : BitString := patternBits 32 1
private def bits255A : BitString := patternBits 255 0
private def bits256A : BitString := patternBits 256 1

private def sliceEmpty : Slice := mkSliceWithBitsRefs #[]
private def slice8A : Slice := mkSliceWithBitsRefs bits8A
private def slice16A : Slice := mkSliceWithBitsRefs bits16A
private def slice32A : Slice := mkSliceWithBitsRefs bits32A
private def slice255A : Slice := mkSliceWithBitsRefs bits255A
private def slice256A : Slice := mkSliceWithBitsRefs bits256A
private def slice8WithRefs : Slice := mkSliceWithBitsRefs bits8A #[refLeafA, refLeafB]
private def slice16WithRefs : Slice := mkSliceWithBitsRefs bits16A #[refLeafC]

private def cursorCell : Cell := Cell.mkOrdinary (patternBits 20 2) #[refLeafA, refLeafB, refLeafC]
private def cursorSlice : Slice := { cell := cursorCell, bitPos := 4, refPos := 1 }      -- 16 bits remaining
private def cursorShortSlice : Slice := { cell := cursorCell, bitPos := 15, refPos := 0 } -- 5 bits remaining

private def sdSubstrSetGasExact : Int :=
  computeExactGasBudget sdSubstrInstr

private def sdSubstrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdSubstrInstr

private def sdskipfirstInstr : Instr := .sdskipfirst

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
  mkSliceWithBitsRefs (patternBits bits phase) (refsByCount refs)

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell refLeafB, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def genSdSubstrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (offs, rng4) := randNat rng3 0 totalBits
    let (bits, rng5) := randNat rng4 0 (totalBits - offs)
    let (phase, rng6) := randNat rng5 0 3
    let s := mkFullSlice totalBits refs phase
    (mkSdSubstrCase s!"fuzz/ok/full/len{totalBits}/offs{offs}/bits{bits}"
      #[.slice s, intV (Int.ofNat offs), intV (Int.ofNat bits)], rng6)
  else if shape = 1 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (offs, rng4) := randNat rng3 0 totalBits
    let (bits, rng5) := randNat rng4 0 (totalBits - offs)
    let (phase, rng6) := randNat rng5 0 3
    let (noise, rng7) := pickNoiseValue rng6
    let s := mkFullSlice totalBits refs phase
    (mkSdSubstrCase "fuzz/ok/deep"
      #[noise, .slice s, intV (Int.ofNat offs), intV (Int.ofNat bits)], rng7)
  else if shape = 2 then
    let (totalBits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    let (skipBits, rng4) := randNat rng3 0 totalBits
    let remBits := totalBits - skipBits
    let (offs, rng5) := randNat rng4 0 remBits
    let (bits, rng6) := randNat rng5 0 (remBits - offs)
    let (phase, rng7) := randNat rng6 0 3
    let s := mkFullSlice totalBits refs phase
    let stack : Array Value := #[.slice s, intV (Int.ofNat skipBits)]
    let program : Array Instr :=
      #[sdskipfirstInstr, .pushInt (.num offs), .pushInt (.num bits), sdSubstrInstr]
    (mkSdSubstrCase s!"fuzz/ok/cursor/skip{skipBits}/offs{offs}/bits{bits}" stack program, rng7)
  else if shape = 3 then
    let (mode, rng2) := randNat rng1 0 1
    let (totalBits0, rng3) := randNat rng2 0 1022
    let (refs, rng4) := pickRefsMixed rng3
    let (phase, rng5) := randNat rng4 0 3
    let s := mkFullSlice totalBits0 refs phase
    if mode = 0 then
      let (offs, rng6) := randNat rng5 0 totalBits0
      let bits := (totalBits0 - offs) + 1
      (mkSdSubstrCase s!"fuzz/cellund/bits+1/len{totalBits0}/offs{offs}"
        #[.slice s, intV (Int.ofNat offs), intV (Int.ofNat bits)], rng6)
    else
      let offs := totalBits0 + 1
      (mkSdSubstrCase s!"fuzz/cellund/offs>len/len{totalBits0}"
        #[.slice s, intV (Int.ofNat offs), intV 0], rng5)
  else if shape = 4 then
    let (n, rng2) := randNat rng1 0 2
    if n = 0 then
      (mkSdSubstrCase "fuzz/underflow/empty" #[], rng2)
    else if n = 1 then
      (mkSdSubstrCase "fuzz/underflow/one" #[.slice slice8A], rng2)
    else
      (mkSdSubstrCase "fuzz/underflow/two" #[.slice slice8A, intV 0], rng2)
  else if shape = 5 then
    let (mode, rng2) := randNat rng1 0 2
    let badBits : Value :=
      if mode = 0 then .null
      else if mode = 1 then .slice sliceEmpty
      else .cell Cell.empty
    (mkSdSubstrCase "fuzz/type/bits" #[.slice slice8A, intV 0, badBits], rng2)
  else if shape = 6 then
    let (mode, rng2) := randNat rng1 0 2
    if mode = 0 then
      (mkSdSubstrCase "fuzz/range/bits"
        #[.slice slice8A, intV 0, intV 1024], rng2)
    else if mode = 1 then
      (mkSdSubstrCase "fuzz/range/offs"
        #[.slice slice8A, intV (-1), intV 0], rng2)
    else
      let stack : Array Value := #[.slice slice8A]
      let program : Array Instr := #[.pushInt .nan, .pushInt (.num 0), sdSubstrInstr]
      (mkSdSubstrCase "fuzz/range/offs-nan" stack program, rng2)
  else
    (mkSdSubstrCase "fuzz/type/slice"
      #[.null, intV 0, intV 0], rng1)

def suite : InstrSuite where
  id := sdSubstrId
  unit := #[
    { name := "unit/direct/success-substring-core-cases"
      run := do
        let checks : Array SubstrCheck :=
          #[
            { label := "ok/empty-0-0", s := sliceEmpty, offs := 0, bits := 0 },
            { label := "ok/head-8-0-4", s := slice8A, offs := 0, bits := 4 },
            { label := "ok/mid-8-2-3", s := slice8A, offs := 2, bits := 3 },
            { label := "ok/tail-8-5-3", s := slice8A, offs := 5, bits := 3 },
            { label := "ok/last-1bit", s := slice8A, offs := 7, bits := 1 },
            { label := "ok/offset-end-zero-width", s := slice8A, offs := 8, bits := 0 },
            { label := "ok/full-16", s := slice16A, offs := 0, bits := 16 },
            { label := "ok/long-edge-255-1", s := slice256A, offs := 255, bits := 1 }
          ]
        for c in checks do
          expectOkStack c.label
            (runSdSubstrDirect #[.slice c.s, intV c.offs, intV c.bits])
            (expectedSubstrStack #[] c.s c.offs c.bits) }
    ,
    { name := "unit/direct/cursor-and-refs-semantics"
      run := do
        let checks : Array SubstrCheck :=
          #[
            { label := "ok/refs-input-dropped", s := slice8WithRefs, offs := 1, bits := 5 },
            { label := "ok/cursor-window-3-6", s := cursorSlice, offs := 3, bits := 6 },
            { label := "ok/cursor-full-remaining", s := cursorSlice, offs := 0, bits := 16 },
            { label := "ok/cursor-tail-zero-width", s := cursorSlice, offs := 16, bits := 0 }
          ]
        for c in checks do
          expectOkStack c.label
            (runSdSubstrDirect #[.slice c.s, intV c.offs, intV c.bits])
            (expectedSubstrStack #[] c.s c.offs c.bits)

        expectOkStack "ok/deep-stack-preserved"
          (runSdSubstrDirect #[.null, intV 77, .slice cursorSlice, intV 2, intV 5])
          (expectedSubstrStack #[.null, intV 77] cursorSlice 2 5) }
    ,
    { name := "unit/direct/cellund-insufficient-bits"
      run := do
        expectErr "cellund/empty-vs-bit1"
          (runSdSubstrDirect #[.slice sliceEmpty, intV 0, intV 1]) .cellUnd
        expectErr "cellund/8-vs-4plus5"
          (runSdSubstrDirect #[.slice slice8A, intV 4, intV 5]) .cellUnd
        expectErr "cellund/offset-beyond-end-even-zero-bits"
          (runSdSubstrDirect #[.slice slice8A, intV 9, intV 0]) .cellUnd
        expectErr "cellund/short-cursor-3plus3"
          (runSdSubstrDirect #[.slice cursorShortSlice, intV 3, intV 3]) .cellUnd
        expectErr "cellund/long-255-vs-256"
          (runSdSubstrDirect #[.slice slice255A, intV 0, intV 256]) .cellUnd }
    ,
    { name := "unit/direct/underflow-type-range-and-error-order"
      run := do
        expectErr "underflow/empty" (runSdSubstrDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSdSubstrDirect #[.slice slice8A]) .stkUnd
        expectErr "underflow/two-items" (runSdSubstrDirect #[.slice slice8A, intV 0]) .stkUnd

        expectErr "type/bits-top-null"
          (runSdSubstrDirect #[.slice slice8A, intV 0, .null]) .typeChk
        expectErr "type/bits-top-cell"
          (runSdSubstrDirect #[.slice slice8A, intV 0, .cell refLeafA]) .typeChk
        expectErr "type/offs-not-int-after-valid-bits"
          (runSdSubstrDirect #[.slice slice8A, .null, intV 0]) .typeChk
        expectErr "type/slice-not-slice-after-valid-nats"
          (runSdSubstrDirect #[.null, intV 0, intV 0]) .typeChk

        expectErr "range/bits-negative"
          (runSdSubstrDirect #[.slice slice8A, intV 0, intV (-1)]) .rangeChk
        expectErr "range/bits-too-large"
          (runSdSubstrDirect #[.slice slice8A, intV 0, intV 1024]) .rangeChk
        expectErr "range/bits-nan"
          (runSdSubstrDirect #[.slice slice8A, intV 0, .int .nan]) .rangeChk
        expectErr "range/offs-negative"
          (runSdSubstrDirect #[.slice slice8A, intV (-1), intV 0]) .rangeChk
        expectErr "range/offs-too-large"
          (runSdSubstrDirect #[.slice slice8A, intV 2048, intV 0]) .rangeChk
        expectErr "range/offs-nan"
          (runSdSubstrDirect #[.slice slice8A, .int .nan, intV 0]) .rangeChk

        expectErr "error-order/range-before-slice-type-via-bits"
          (runSdSubstrDirect #[.null, intV 0, intV 2048]) .rangeChk
        expectErr "error-order/type-before-slice-type-via-bits"
          (runSdSubstrDirect #[.null, intV 0, .null]) .typeChk
        expectErr "error-order/range-before-slice-type-via-offs"
          (runSdSubstrDirect #[.null, intV (-1), intV 0]) .rangeChk
        expectErr "error-order/type-before-slice-type-via-offs"
          (runSdSubstrDirect #[.null, .null, intV 0]) .typeChk }
    ,
    { name := "unit/model/alignment-on-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-0-0", #[.slice sliceEmpty, intV 0, intV 0]),
            ("ok/mid-8-2-3", #[.slice slice8A, intV 2, intV 3]),
            ("ok/deep-preserve", #[.null, intV 9, .slice slice16WithRefs, intV 4, intV 6]),
            ("ok/refs-input", #[.slice slice8WithRefs, intV 1, intV 5]),
            ("ok/cursor-window", #[.slice cursorSlice, intV 3, intV 6]),
            ("err/cellund", #[.slice slice8A, intV 6, intV 3]),
            ("err/underflow", #[]),
            ("err/type-bits", #[.slice slice8A, intV 0, .null]),
            ("err/type-offs", #[.slice slice8A, .null, intV 0]),
            ("err/range-bits", #[.slice slice8A, intV 0, intV 1024]),
            ("err/range-offs", #[.slice slice8A, intV 1024, intV 0]),
            ("err/order-range-before-slice-type", #[.null, intV 0, intV 2048])
          ]
        for (label, stack) in samples do
          expectSameOutcome s!"model/{label}"
            (runSdSubstrDirect stack)
            (runSdSubstrModel stack) }
    ,
    { name := "unit/opcode/decode-assembler-boundaries-and-gap"
      run := do
        let assembled ←
          match assembleCp0 [sdSubstrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sdsubstr failed: {e}")
        if assembled.bits = natToBits sdsubstrWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdsubstr: expected opcode 0xd724, got bits {assembled.bits}")
        if assembled.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdsubstr: expected 16 bits, got {assembled.bits.size}")

        let program : Array Instr := #[
          .sdskiplast,
          sdSubstrInstr,
          .sdBeginsX false,
          .sdBeginsX true,
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdskiplast-neighbor" s0 .sdskiplast 16
        let s2 ← expectDecodeStep "decode/sdsubstr" s1 sdSubstrInstr 16
        let s3 ← expectDecodeStep "decode/sdbeginsx-neighbor" s2 (.sdBeginsX false) 16
        let s4 ← expectDecodeStep "decode/sdbeginsxq-neighbor" s3 (.sdBeginsX true) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let raw := mkSliceFromBits
          (natToBits sdskiplastWord 16 ++ natToBits sdsubstrWord 16 ++
            natToBits sdbeginsxWord 16 ++ natToBits sdbeginsxqWord 16 ++ addCell.bits)
        let r1 ← expectDecodeStep "decode/raw-sdskiplast" raw .sdskiplast 16
        let r2 ← expectDecodeStep "decode/raw-sdsubstr" r1 sdSubstrInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdbeginsx" r2 (.sdBeginsX false) 16
        let r4 ← expectDecodeStep "decode/raw-sdbeginsxq" r3 (.sdBeginsX true) 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-0xd725"
          (mkSliceFromBits (natToBits 0xd725 16))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-sdsubstr-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runSdSubstrDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-sdskiplast"
          (runSdSubstrDispatchFallback .sdskiplast #[intV 7])
          #[intV 7, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-scutfirst"
          (runSdSubstrDispatchFallback (.cellOp .scutfirst) #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-sdpsfx"
          (runSdSubstrDispatchFallback (.cellOp .sdPsfx) #[.slice slice8A])
          #[.slice slice8A, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdSubstrCase "ok/empty-0-0"
      #[.slice sliceEmpty, intV 0, intV 0],
    mkSdSubstrCase "ok/8-head-0-4"
      #[.slice slice8A, intV 0, intV 4],
    mkSdSubstrCase "ok/8-mid-2-3"
      #[.slice slice8A, intV 2, intV 3],
    mkSdSubstrCase "ok/8-tail-5-3"
      #[.slice slice8A, intV 5, intV 3],
    mkSdSubstrCase "ok/8-last-7-1"
      #[.slice slice8A, intV 7, intV 1],
    mkSdSubstrCase "ok/8-offset-end-zero-width"
      #[.slice slice8A, intV 8, intV 0],
    mkSdSubstrCase "ok/16-full"
      #[.slice slice16A, intV 0, intV 16],
    mkSdSubstrCase "ok/32-window-9-12"
      #[.slice slice32A, intV 9, intV 12],
    mkSdSubstrCase "ok/256-edge-255-1"
      #[.slice slice256A, intV 255, intV 1],
    mkSdSubstrCase "ok/refs-input-dropped"
      #[.slice slice8WithRefs, intV 1, intV 5],
    mkSdSubstrCase "ok/deep-stack-preserve"
      #[.null, intV 42, .slice slice16WithRefs, intV 4, intV 6],

    mkSdSubstrCase "cellund/empty-vs-bit1"
      #[.slice sliceEmpty, intV 0, intV 1],
    mkSdSubstrCase "cellund/8-vs-4plus5"
      #[.slice slice8A, intV 4, intV 5],
    mkSdSubstrCase "cellund/offset-beyond-end-even-zero-width"
      #[.slice slice8A, intV 9, intV 0],

    mkSdSubstrCase "underflow/empty" #[],
    mkSdSubstrCase "underflow/one-item"
      #[.slice slice8A],

    mkSdSubstrCase "type/bits-top-null"
      #[.slice slice8A, intV 0, .null],
    mkSdSubstrCase "type/slice-not-slice-after-valid-nats"
      #[.null, intV 0, intV 0],

    mkSdSubstrCase "range/bits-too-large-1024"
      #[.slice slice8A, intV 0, intV 1024],
    mkSdSubstrCase "range/offs-negative"
      #[.slice slice8A, intV (-1), intV 0],

    mkSdSubstrCase "error-order/range-before-slice-type-via-bits"
      #[.null, intV 0, intV 2048],

    mkSdSubstrCase "gas/exact-cost-succeeds"
      #[.slice slice16A, intV 2, intV 5]
      #[.pushInt (.num sdSubstrSetGasExact), .tonEnvOp .setGasLimit, sdSubstrInstr],
    mkSdSubstrCase "gas/exact-minus-one-out-of-gas"
      #[.slice slice16A, intV 2, intV 5]
      #[.pushInt (.num sdSubstrSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdSubstrInstr]
  ]
  fuzz := #[
    { seed := 2026021114
      count := 500
      gen := genSdSubstrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDSUBSTR
