import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BREMREFS

/-
BREMREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bremrefs.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xcf36` encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf36` decode to `.cellOp .bremrefs`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_int_builder_func`, opcode `0xcf36`, pushes `4 - b->size_refs()`).

Branch contracts covered in this suite:
- dispatch: only `.cellOp .bremrefs` is handled, everything else falls through to `next`;
- stack behavior: `popBuilder` gives `stkUnd` on empty stack, `typeChk` on non-builder top;
- success path: pushes one int `4 - refs` (bits ignored) and preserves lower stack;
- decode/assembler boundary: canonical `0xcf36` in the `0xcf3x` family, with
  neighbor opcodes `0xcf35/0xcf37`, `0xcf38xx` immediate boundary, and `0xcf34` gap.

Harness note:
- oracle stack tokens cannot encode non-empty builders; oracle/fuzz success cases build
  non-empty builders in-program and keep `initStack` oracle-serializable.
-/

private def bremrefsId : InstrId := { name := "BREMREFS" }

private def bremrefsInstr : Instr := .cellOp .bremrefs

private def bremrefsWord : Nat := 0xcf36

private def dispatchSentinel : Int := 536

private def execInstrCellOpBremrefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBremrefs op next
  | _ => next

private def mkBremrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bremrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bremrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBremrefsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bremrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBremrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBremrefsOnly bremrefsInstr stack

private def runBremrefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBremrefsOnly instr (VM.push (intV dispatchSentinel)) stack

private def bremrefsSetGasExact : Int :=
  computeExactGasBudget bremrefsInstr

private def bremrefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bremrefsInstr

private def patternBits (n : Nat) (phase : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    let bit := ((i + phase) % 2 == 1) || ((i + phase) % 5 == 0)
    out := out.push bit
  return out

private def refCellA : Cell :=
  Cell.empty

private def refCellB : Cell :=
  Cell.mkOrdinary (patternBits 3 1) #[]

private def refCellC : Cell :=
  Cell.mkOrdinary (patternBits 6 2) #[refCellA]

private def refCellD : Cell :=
  Cell.mkOrdinary (patternBits 1 3) #[refCellB]

private def refCellPool : Array Cell :=
  #[refCellA, refCellB, refCellC, refCellD]

private def mkRefArray (count : Nat) : Array Cell := Id.run do
  let mut refs : Array Cell := #[]
  for i in [0:count] do
    refs := refs.push (refCellPool[i % refCellPool.size]!)
  return refs

private def mkBuilderWithSizes (bitCount refCount : Nat) (phase : Nat := 0) : Builder :=
  { (Builder.empty.storeBits (patternBits bitCount phase)) with refs := mkRefArray refCount }

private def mkFullSlice (bitCount : Nat) (phase : Nat := 0) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternBits bitCount phase) refs)

private def fullSliceNoiseA : Slice :=
  mkFullSlice 9 1 #[refCellA]

private def fullSliceNoiseB : Slice :=
  mkFullSlice 7 0 #[refCellB]

private def expectedBremrefsOut (below : Array Value) (b : Builder) : Array Value :=
  below ++ #[intV (Int.ofNat (4 - b.refs.size))]

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkBremrefsProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[bremrefsInstr]

private def mkBremrefsSizedProgramCase
    (name : String)
    (below : Array Value)
    (bits refs : Nat) : OracleCase :=
  mkBremrefsProgramCase name below (mkBremrefsProgram bits refs)

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

private def bchkBitsImmWord (bits : Nat) (quiet : Bool) : Nat :=
  let base : Nat := if quiet then 0xcf3c else 0xcf38
  (base <<< 8) + (bits - 1)

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 768, 1023]

private def pickBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsBoundaryPool.size - 1)
  (bitsBoundaryPool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 4

private def pickNoiseValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 6
  let out : Value × String :=
    if pick = 0 then
      (.null, "null")
    else if pick = 1 then
      (intV 73, "int")
    else if pick = 2 then
      (.cell refCellB, "cell")
    else if pick = 3 then
      (.slice fullSliceNoiseA, "sliceA")
    else if pick = 4 then
      (.tuple #[], "tuple")
    else if pick = 5 then
      (.slice fullSliceNoiseB, "sliceB")
    else
      (.cell refCellD, "cellD")
  (out.1, out.2, rng1)

private def genBremrefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    (mkBremrefsCase "fuzz/ok/direct-empty-builder" #[.builder Builder.empty], rng1)
  else if shape = 1 then
    let (bits, rng2) := pickBitsBoundary rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBremrefsSizedProgramCase s!"fuzz/ok/program-boundary/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 2 then
    let (bits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBremrefsSizedProgramCase s!"fuzz/ok/program-mixed/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 3 then
    let (noise, tag, rng2) := pickNoiseValue rng1
    let (bits, rng3) := pickBitsMixed rng2
    let (refs, rng4) := pickRefsMixed rng3
    (mkBremrefsSizedProgramCase s!"fuzz/ok/deep1-{tag}/bits-{bits}/refs-{refs}" #[noise] bits refs, rng4)
  else if shape = 4 then
    let (noise1, tag1, rng2) := pickNoiseValue rng1
    let (noise2, tag2, rng3) := pickNoiseValue rng2
    let (bits, rng4) := pickBitsMixed rng3
    let (refs, rng5) := pickRefsMixed rng4
    (mkBremrefsSizedProgramCase s!"fuzz/ok/deep2-{tag1}-{tag2}/bits-{bits}/refs-{refs}"
      #[noise1, noise2] bits refs, rng5)
  else if shape = 5 then
    (mkBremrefsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkBremrefsCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 7 then
    let (n, rng2) := randNat rng1 0 255
    (mkBremrefsCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
  else if shape = 8 then
    (mkBremrefsCase "fuzz/type/top-cell" #[.cell refCellC], rng1)
  else if shape = 9 then
    (mkBremrefsCase "fuzz/type/top-slice-full" #[.slice fullSliceNoiseA], rng1)
  else if shape = 10 then
    (mkBremrefsCase "fuzz/type/top-tuple-empty" #[.tuple #[]], rng1)
  else if shape = 11 then
    let (noise, tag, rng2) := pickNoiseValue rng1
    (mkBremrefsCase s!"fuzz/type/deep-top-not-builder-{tag}" #[.builder Builder.empty, noise], rng2)
  else if shape = 12 then
    (mkBremrefsCase "fuzz/gas/exact"
      #[.builder Builder.empty]
      #[.pushInt (.num bremrefsSetGasExact), .tonEnvOp .setGasLimit, bremrefsInstr], rng1)
  else if shape = 13 then
    (mkBremrefsCase "fuzz/gas/exact-minus-one"
      #[.builder Builder.empty]
      #[.pushInt (.num bremrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bremrefsInstr], rng1)
  else if shape = 14 then
    let (bits, rng2) := pickBitsMixed rng1
    (mkBremrefsSizedProgramCase s!"fuzz/ok/max-refs4/bits-{bits}" #[] bits 4, rng2)
  else
    (mkBremrefsSizedProgramCase "fuzz/ok/max-bits-refs/bits-1023-refs4" #[.null] 1023 4, rng1)

def suite : InstrSuite where
  id := bremrefsId
  unit := #[
    { name := "unit/direct/remaining-refs-success-and-boundaries"
      run := do
        let builders : Array Builder :=
          #[
            Builder.empty,
            mkBuilderWithSizes 7 1,
            mkBuilderWithSizes 32 2 1,
            mkBuilderWithSizes 1023 3 2,
            mkBuilderWithSizes 15 4
          ]
        for i in [0:builders.size] do
          let b ←
            match builders[i]? with
            | some b => pure b
            | none => throw (IO.userError s!"builders index out of bounds: {i}")
          expectOkStack s!"ok/case-{i}/bits-{b.bits.size}/refs-{b.refs.size}"
            (runBremrefsDirect #[.builder b])
            (expectedBremrefsOut #[] b)

        let below : Array Value := #[.null, intV 91, .slice fullSliceNoiseA]
        let deepBuilder := mkBuilderWithSizes 255 2
        expectOkStack "ok/deep-stack-preserve-below"
          (runBremrefsDirect (below ++ #[.builder deepBuilder]))
          (expectedBremrefsOut below deepBuilder) }
    ,
    { name := "unit/direct/pop-order-top-builder-controls-output"
      run := do
        let low := mkBuilderWithSizes 9 1
        let high := mkBuilderWithSizes 37 3
        expectOkStack "order/two-builders-pop-top"
          (runBremrefsDirect #[.builder low, .builder high])
          #[.builder low, intV 1]

        let below : Array Value := #[.cell refCellA, .slice fullSliceNoiseB]
        let top := mkBuilderWithSizes 511 4
        expectOkStack "order/deep-stack-only-top-builder-popped"
          (runBremrefsDirect (below ++ #[.builder top]))
          (below ++ #[intV 0]) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runBremrefsDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runBremrefsDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runBremrefsDirect #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runBremrefsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice-full"
          (runBremrefsDirect #[.slice fullSliceNoiseA]) .typeChk
        expectErr "type/top-tuple-empty"
          (runBremrefsDirect #[.tuple #[]]) .typeChk

        expectErr "type/deep-top-not-builder"
          (runBremrefsDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/range-cellov-intov-unreachable"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBremrefsDirect #[.builder (mkBuilderWithSizes 17 2)]),
            ("underflow", runBremrefsDirect #[]),
            ("type", runBremrefsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BREMREFS")
          | .error .cellOv =>
              throw (IO.userError s!"{p.1}: unexpected cellOv for BREMREFS")
          | .error .intOv =>
              throw (IO.userError s!"{p.1}: unexpected intOv for BREMREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-boundary-and-gap"
      run := do
        let single ←
          match assembleCp0 [bremrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble bremrefs failed: {e}")
        if single.bits = natToBits bremrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/bremrefs: expected 0xcf36 encoding, got bits {single.bits}")
        if single.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/bremrefs: expected 16-bit encoding, got {single.bits.size}")

        let program : Array Instr := #[
          .cellOp .brembits,
          bremrefsInstr,
          .cellOp .brembitrefs,
          .cellOp (.bchkBitsImm 1 false),
          .add
        ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/brembits" s0 (.cellOp .brembits) 16
        let s2 ← expectDecodeStep "decode/bremrefs" s1 bremrefsInstr 16
        let s3 ← expectDecodeStep "decode/brembitrefs" s2 (.cellOp .brembitrefs) 16
        let s4 ← expectDecodeStep "decode/bchkbits-imm1" s3 (.cellOp (.bchkBitsImm 1 false)) 24
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/family-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xcf35 16 ++
            natToBits 0xcf36 16 ++
            natToBits 0xcf37 16 ++
            natToBits (bchkBitsImmWord 1 false) 24 ++
            addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xcf35-brembits" r0 (.cellOp .brembits) 16
        let r2 ← expectDecodeStep "decode/raw-0xcf36-bremrefs" r1 bremrefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-0xcf37-brembitrefs" r2 (.cellOp .brembitrefs) 16
        let r4 ← expectDecodeStep "decode/raw-0xcf38xx-bchkbits-imm1" r3 (.cellOp (.bchkBitsImm 1 false)) 24
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-cf34"
          (mkSliceFromBits (natToBits 0xcf34 16))
          .invOpcode }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runBremrefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-bbits"
          (runBremrefsDispatchFallback .bbits #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-brefs"
          (runBremrefsDispatchFallback (.cellOp .brefs) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-brembits"
          (runBremrefsDispatchFallback (.cellOp .brembits) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
  ]
  oracle := #[
    mkBremrefsCase "ok/direct-empty-builder"
      #[.builder Builder.empty],
    mkBremrefsCase "ok/direct-deep-null"
      #[.null, .builder Builder.empty],
    mkBremrefsCase "ok/direct-deep-int"
      #[intV 77, .builder Builder.empty],
    mkBremrefsCase "ok/direct-deep-full-slice"
      #[.slice fullSliceNoiseA, .builder Builder.empty],

    mkBremrefsSizedProgramCase "ok/program/bits0-refs1"
      #[] 0 1,
    mkBremrefsSizedProgramCase "ok/program/bits1-refs0"
      #[] 1 0,
    mkBremrefsSizedProgramCase "ok/program/bits7-refs2"
      #[] 7 2,
    mkBremrefsSizedProgramCase "ok/program/bits8-refs3"
      #[] 8 3,
    mkBremrefsSizedProgramCase "ok/program/bits15-refs4"
      #[] 15 4,
    mkBremrefsSizedProgramCase "ok/program/bits127-refs1"
      #[] 127 1,
    mkBremrefsSizedProgramCase "ok/program/bits256-refs2"
      #[] 256 2,
    mkBremrefsSizedProgramCase "ok/program/bits511-refs3"
      #[] 511 3,
    mkBremrefsSizedProgramCase "ok/program/bits1023-refs4"
      #[] 1023 4,
    mkBremrefsSizedProgramCase "ok/program/deep-null/bits9-refs3"
      #[.null] 9 3,
    mkBremrefsSizedProgramCase "ok/program/deep-int-cell/bits33-refs2"
      #[intV (-9), .cell refCellA] 33 2,

    mkBremrefsCase "underflow/empty"
      #[],
    mkBremrefsCase "type/top-null"
      #[.null],
    mkBremrefsCase "type/top-int"
      #[intV 12],
    mkBremrefsCase "type/top-cell"
      #[.cell refCellC],
    mkBremrefsCase "type/top-slice-full"
      #[.slice fullSliceNoiseA],
    mkBremrefsCase "type/top-tuple-empty"
      #[.tuple #[]],
    mkBremrefsCase "type/deep-top-not-builder-builder-below"
      #[.builder Builder.empty, .null],

    mkBremrefsCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num bremrefsSetGasExact), .tonEnvOp .setGasLimit, bremrefsInstr],
    mkBremrefsCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num bremrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bremrefsInstr]
  ]
  fuzz := #[
    { seed := 2026021094
      count := 320
      gen := genBremrefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BREMREFS
