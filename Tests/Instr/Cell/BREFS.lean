import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BREFS

/-
BREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Brefs.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xcf32` encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf32` decode to `.cellOp .brefs`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_int_builder_func`, opcode `0xcf32`, pushes `size_refs()`).

Branch map covered by this suite:
- dispatch fallthrough (`.cellOp .brefs` arm vs `next`);
- `popBuilder` underflow and strict top-type checks;
- success path contract: `... builder -> ... refs` (single int, bits ignored);
- opcode/decode boundaries around `0xcf32` and immediate neighbors.

Harness note:
- oracle stack tokens cannot encode non-empty builders; non-empty builder success
  cases are constructed inside `program` via `NEWC` + `STU` + `STREF`.
-/

private def brefsId : InstrId := { name := "BREFS" }

private def brefsInstr : Instr := .cellOp .brefs

private def brefsWord : Nat := 0xcf32

private def dispatchSentinel : Int := 932

private def execInstrCellOpBrefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBrefs op next
  | _ => next

private def mkBrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[brefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := brefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBrefsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := brefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBrefsOnly brefsInstr stack

private def runBrefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBrefsOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def brefsSetGasExact : Int :=
  computeExactGasBudget brefsInstr

private def brefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne brefsInstr

private def patternBits (n : Nat) (phase : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    let bit := ((i + phase) % 3 = 1) || ((i + phase) % 5 = 0)
    out := out.push bit
  return out

private def refCellA : Cell :=
  Cell.empty

private def refCellB : Cell :=
  Cell.mkOrdinary (patternBits 3 1) #[]

private def refCellC : Cell :=
  Cell.mkOrdinary (patternBits 6 2) #[Cell.empty]

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

private def builderEmpty : Builder :=
  Builder.empty

private def builderBits9Refs0 : Builder :=
  mkBuilderWithSizes 9 0

private def builderBits0Refs3 : Builder :=
  { Builder.empty with refs := mkRefArray 3 }

private def builderBits17Refs2 : Builder :=
  mkBuilderWithSizes 17 2 1

private def builderBits257Refs1 : Builder :=
  mkBuilderWithSizes 257 1 2

private def builderBits1023Refs4 : Builder :=
  { fullBuilder1023 with refs := mkRefArray 4 }

private def fullSliceNoiseA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternBits 7 1) #[refCellA])

private def fullSliceNoiseB : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[refCellB, refCellC])

private def expectedBrefsOut (below : Array Value) (b : Builder) : Array Value :=
  below ++ #[intV (Int.ofNat b.refs.size)]

private def appendBitsToTopBuilder (bits : Nat) (x : IntVal := .num 0) : Array Instr :=
  Id.run do
    let mut out : Array Instr := #[]
    let mut rem := bits
    while rem > 0 do
      let chunk : Nat := Nat.min 256 rem
      out := out ++ #[.pushInt x, .xchg0 1, .stu chunk]
      rem := rem - chunk
    return out

private def appendOneRefToTopBuilder : Array Instr :=
  #[.newc, .endc, .xchg0 1, .stref]

private def appendRefsToTopBuilder : Nat → Array Instr
  | 0 => #[]
  | n + 1 => appendRefsToTopBuilder n ++ appendOneRefToTopBuilder

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkBrefsProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[brefsInstr]

private def mkBrefsSizedProgramCase
    (name : String)
    (below : Array Value)
    (bits refs : Nat) : OracleCase :=
  mkBrefsProgramCase name below (mkBrefsProgram bits refs)

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
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), "int", rng2)
  else if pick = 2 then
    (.cell refCellB, "cell", rng1)
  else if pick = 3 then
    (.slice fullSliceNoiseA, "slice-a", rng1)
  else if pick = 4 then
    (.tuple #[], "tuple", rng1)
  else
    (.slice fullSliceNoiseB, "slice-b", rng1)

private def pickBadTopValue (rng0 : StdGen) : Value × String × StdGen :=
  let (pick, rng1) := randNat rng0 0 4
  if pick = 0 then
    (.null, "null", rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 255
    (intV (Int.ofNat n - 128), "int", rng2)
  else if pick = 2 then
    (.cell refCellC, "cell", rng1)
  else if pick = 3 then
    (.slice fullSliceNoiseA, "slice", rng1)
  else
    (.tuple #[], "tuple", rng1)

private def genBrefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 17
  let (case0, rng2) :=
    if shape = 0 then
      (mkBrefsCase "fuzz/ok/direct-empty-builder" #[.builder Builder.empty], rng1)
    else if shape = 1 then
      let (bits, rng2) := pickBitsBoundary rng1
      let (refs, rng3) := pickRefsMixed rng2
      (mkBrefsSizedProgramCase s!"fuzz/ok/program-boundary/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
    else if shape = 2 then
      let (bits, rng2) := randNat rng1 0 128
      let (refs, rng3) := pickRefsMixed rng2
      (mkBrefsSizedProgramCase s!"fuzz/ok/program-small/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
    else if shape = 3 then
      let (bits, rng2) := randNat rng1 257 1023
      let (refs, rng3) := pickRefsMixed rng2
      (mkBrefsSizedProgramCase s!"fuzz/ok/program-high/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
    else if shape = 4 then
      let (refs, rng2) := randNat rng1 1 4
      (mkBrefsSizedProgramCase s!"fuzz/ok/program-refs-only/refs-{refs}" #[] 0 refs, rng2)
    else if shape = 5 then
      let (bits, rng2) := pickBitsMixed rng1
      (mkBrefsSizedProgramCase s!"fuzz/ok/program-bits-only/bits-{bits}" #[] bits 0, rng2)
    else if shape = 6 then
      let (noise, tag, rng2) := pickNoiseValue rng1
      let (bits, rng3) := pickBitsMixed rng2
      let (refs, rng4) := pickRefsMixed rng3
      (mkBrefsSizedProgramCase s!"fuzz/ok/deep1-{tag}/bits-{bits}/refs-{refs}" #[noise] bits refs, rng4)
    else if shape = 7 then
      let (noise1, tag1, rng2) := pickNoiseValue rng1
      let (noise2, tag2, rng3) := pickNoiseValue rng2
      let (bits, rng4) := pickBitsMixed rng3
      let (refs, rng5) := pickRefsMixed rng4
      (mkBrefsSizedProgramCase s!"fuzz/ok/deep2-{tag1}-{tag2}/bits-{bits}/refs-{refs}" #[noise1, noise2] bits refs, rng5)
    else if shape = 8 then
      (mkBrefsCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 9 then
      (mkBrefsCase "fuzz/type/top-null" #[.null], rng1)
    else if shape = 10 then
      let (n, rng2) := randNat rng1 0 255
      (mkBrefsCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
    else if shape = 11 then
      (mkBrefsCase "fuzz/type/top-cell" #[.cell refCellD], rng1)
    else if shape = 12 then
      (mkBrefsCase "fuzz/type/top-slice-full" #[.slice fullSliceNoiseA], rng1)
    else if shape = 13 then
      (mkBrefsCase "fuzz/type/top-tuple-empty" #[.tuple #[]], rng1)
    else if shape = 14 then
      let (bad, badTag, rng2) := pickBadTopValue rng1
      (mkBrefsCase s!"fuzz/type/deep-top-not-builder-{badTag}" #[.builder Builder.empty, bad], rng2)
    else if shape = 15 then
      (mkBrefsCase "fuzz/gas/exact"
        #[.builder Builder.empty]
        #[.pushInt (.num brefsSetGasExact), .tonEnvOp .setGasLimit, brefsInstr], rng1)
    else if shape = 16 then
      (mkBrefsCase "fuzz/gas/exact-minus-one"
        #[.builder Builder.empty]
        #[.pushInt (.num brefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brefsInstr], rng1)
    else
      (mkBrefsSizedProgramCase "fuzz/ok/stress-max/bits-1023-refs-4" #[.null] 1023 4, rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleDirectCases : Array OracleCase :=
  #[
    mkBrefsCase "ok/direct-empty-builder" #[.builder Builder.empty],
    mkBrefsCase "ok/direct-deep-null" #[.null, .builder Builder.empty],
    mkBrefsCase "ok/direct-deep-int" #[intV 77, .builder Builder.empty],
    mkBrefsCase "ok/direct-deep-cell" #[.cell refCellA, .builder Builder.empty],
    mkBrefsCase "ok/direct-deep-slice" #[.slice fullSliceNoiseA, .builder Builder.empty]
  ]

private def oracleProgramCases : Array OracleCase :=
  #[
    mkBrefsSizedProgramCase "ok/program/refs-only-1" #[] 0 1,
    mkBrefsSizedProgramCase "ok/program/refs-only-4" #[] 0 4,
    mkBrefsSizedProgramCase "ok/program/bits1-refs1" #[] 1 1,
    mkBrefsSizedProgramCase "ok/program/bits8-refs2" #[] 8 2,
    mkBrefsSizedProgramCase "ok/program/bits31-refs3" #[] 31 3,
    mkBrefsSizedProgramCase "ok/program/bits32-refs4" #[] 32 4,
    mkBrefsSizedProgramCase "ok/program/bits255-refs2" #[] 255 2,
    mkBrefsSizedProgramCase "ok/program/bits256-refs4" #[] 256 4,
    mkBrefsSizedProgramCase "ok/program/bits1023-refs1" #[] 1023 1,
    mkBrefsSizedProgramCase "ok/program/deep-slice-tuple/bits63-refs3"
      #[.slice fullSliceNoiseB, .tuple #[]] 63 3
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkBrefsCase "underflow/empty" #[],
    mkBrefsCase "type/top-null" #[.null],
    mkBrefsCase "type/top-int" #[intV 5],
    mkBrefsCase "type/top-cell" #[.cell refCellB],
    mkBrefsCase "type/top-slice-full" #[.slice fullSliceNoiseA],
    mkBrefsCase "type/top-tuple-empty" #[.tuple #[]],
    mkBrefsCase "error-order/top-null-over-builder" #[.builder Builder.empty, .null],
    mkBrefsCase "error-order/top-cell-over-builder" #[.builder Builder.empty, .cell refCellC]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkBrefsCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num brefsSetGasExact), .tonEnvOp .setGasLimit, brefsInstr],
    mkBrefsCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num brefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brefsInstr]
  ]

def suite : InstrSuite where
  id := { name := "BREFS" }
  unit := #[
    { name := "unit/direct/success-ref-count-and-bits-ignored"
      run := do
        expectOkStack "ok/empty-builder"
          (runBrefsDirect #[.builder builderEmpty])
          (expectedBrefsOut #[] builderEmpty)

        expectOkStack "ok/bits9-refs0"
          (runBrefsDirect #[.builder builderBits9Refs0])
          (expectedBrefsOut #[] builderBits9Refs0)

        expectOkStack "ok/bits0-refs3"
          (runBrefsDirect #[.builder builderBits0Refs3])
          (expectedBrefsOut #[] builderBits0Refs3)

        expectOkStack "ok/bits17-refs2"
          (runBrefsDirect #[.builder builderBits17Refs2])
          (expectedBrefsOut #[] builderBits17Refs2)

        expectOkStack "ok/bits257-refs1"
          (runBrefsDirect #[.builder builderBits257Refs1])
          (expectedBrefsOut #[] builderBits257Refs1)

        expectOkStack "ok/bits1023-refs4"
          (runBrefsDirect #[.builder builderBits1023Refs4])
          (expectedBrefsOut #[] builderBits1023Refs4)

        expectOkStack "ok/deep-stack-preserved"
          (runBrefsDirect #[.null, intV 91, .builder builderBits17Refs2])
          (expectedBrefsOut #[.null, intV 91] builderBits17Refs2) }
    ,
    { name := "unit/direct/pop-order-top-builder-controls-result"
      run := do
        let low := mkBuilderWithSizes 5 1
        let high := mkBuilderWithSizes 37 3 2
        expectOkStack "order/two-builders-pop-top"
          (runBrefsDirect #[.builder low, .builder high])
          #[.builder low, intV 3]

        let below : Array Value := #[.cell refCellA, .slice fullSliceNoiseB]
        let top := mkBuilderWithSizes 255 4 1
        expectOkStack "order/deep-stack-only-top-builder-popped"
          (runBrefsDirect (below ++ #[.builder top]))
          (below ++ #[intV 4]) }
    ,
    { name := "unit/direct/underflow-type-and-error-order"
      run := do
        expectErr "underflow/empty" (runBrefsDirect #[]) .stkUnd
        expectErr "type/top-null" (runBrefsDirect #[.null]) .typeChk
        expectErr "type/top-int" (runBrefsDirect #[intV 1]) .typeChk
        expectErr "type/top-cell" (runBrefsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice-full" (runBrefsDirect #[.slice fullSliceNoiseA]) .typeChk
        expectErr "type/top-tuple-empty" (runBrefsDirect #[.tuple #[]]) .typeChk
        expectErr "error-order/top-not-builder-over-builder"
          (runBrefsDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-brefs"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBrefsDirect #[.builder builderBits17Refs2]),
            ("underflow", runBrefsDirect #[]),
            ("type", runBrefsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-boundary-and-gap"
      run := do
        let familyProgram : Array Instr := #[
          .cellOp .bdepth,
          .bbits,
          brefsInstr,
          .cellOp .bbitrefs,
          .cellOp .bremrefs,
          .add
        ]
        let familyCode ←
          match assembleCp0 familyProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let f0 := Slice.ofCell familyCode
        let f1 ← expectDecodeStep "decode/bdepth" f0 (.cellOp .bdepth) 16
        let f2 ← expectDecodeStep "decode/bbits" f1 .bbits 16
        let f3 ← expectDecodeStep "decode/brefs" f2 brefsInstr 16
        let f4 ← expectDecodeStep "decode/bbitrefs" f3 (.cellOp .bbitrefs) 16
        let f5 ← expectDecodeStep "decode/bremrefs" f4 (.cellOp .bremrefs) 16
        let f6 ← expectDecodeStep "decode/tail-add" f5 .add 8
        if f6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/family-end: expected exhausted slice, got {f6.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [brefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits brefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/brefs: expected 0xcf32 encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/brefs: expected 16-bit encoding, got {singleCode.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits 0xcf31 16 ++ natToBits brefsWord 16 ++ natToBits 0xcf33 16 ++ addCell.bits) #[]
        let r0 := Slice.ofCell rawBoundary
        let r1 ← expectDecodeStep "decode/raw-0xcf31-bbits" r0 .bbits 16
        let r2 ← expectDecodeStep "decode/raw-0xcf32-brefs" r1 brefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-0xcf33-bbitrefs" r2 (.cellOp .bbitrefs) 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-cf34"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xcf34 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-brefs-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runBrefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-bbits"
          (runBrefsDispatchFallback .bbits #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bbitrefs"
          (runBrefsDispatchFallback (.cellOp .bbitrefs) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bremrefs"
          (runBrefsDispatchFallback (.cellOp .bremrefs) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
  ]
  oracle := oracleDirectCases ++ oracleProgramCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021097
      count := 300
      gen := genBrefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BREFS
