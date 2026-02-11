import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BBITREFS

/-!
BBITREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Bbitrefs.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xcf33` encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf33` decode to `.cellOp .bbitrefs`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_2int_builder_func`, opcode registration `0xcf33`, pushes `(size, size_refs)`).

Branch map covered by this suite:
- instruction/cell-op guard dispatch fallthrough;
- `popBuilder` underflow and strict top-type checks;
- success path output contract and order:
  `... builder -> ... bits refs` (refs on top, bits below);
- decode/assembler boundaries around `0xcf33` and immediate family neighbors.

Harness note:
- oracle stack tokens cannot encode non-empty builders; oracle/fuzz success cases build
  non-empty builders inside `program` and keep `initStack` oracle-serializable.
-/

private def bbitrefsId : InstrId := { name := "BBITREFS" }

private def bbitrefsInstr : Instr := .cellOp .bbitrefs

private def bbitrefsWord : Nat := 0xcf33

private def dispatchSentinel : Int := 533

private def execInstrCellOpBbitrefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBbitrefs op next
  | _ => next

private def mkBbitrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[bbitrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBbitrefsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := bbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBbitrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBbitrefsOnly bbitrefsInstr stack

private def runBbitrefsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBbitrefsOnly instr (VM.push (intV dispatchSentinel)) stack

private def bbitrefsSetGasExact : Int :=
  computeExactGasBudget bbitrefsInstr

private def bbitrefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne bbitrefsInstr

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

private def expectedBbitrefsOut (below : Array Value) (b : Builder) : Array Value :=
  below ++ #[intV (Int.ofNat b.bits.size), intV (Int.ofNat b.refs.size)]

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkBbitrefsProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[bbitrefsInstr]

private def mkBbitrefsSizedProgramCase
    (name : String)
    (below : Array Value)
    (bits refs : Nat) : OracleCase :=
  mkBbitrefsProgramCase name below (mkBbitrefsProgram bits refs)

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

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 6
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if pick = 2 then
    (.cell refCellB, rng1)
  else if pick = 3 then
    (.slice fullSliceNoiseA, rng1)
  else if pick = 4 then
    (.tuple #[], rng1)
  else if pick = 5 then
    (.slice fullSliceNoiseB, rng1)
  else
    (.cell refCellD, rng1)

private def genBbitrefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    (mkBbitrefsCase "fuzz/ok/direct-empty-builder" #[.builder Builder.empty], rng1)
  else if shape = 1 then
    let (bits, rng2) := pickBitsBoundary rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/program-boundary/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 2 then
    let (bits, rng2) := randNat rng1 0 128
    let (refs, rng3) := pickRefsMixed rng2
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/program-small/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 3 then
    let (bits, rng2) := randNat rng1 257 1023
    let (refs, rng3) := pickRefsMixed rng2
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/program-high/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 4 then
    let (refs, rng2) := pickRefsMixed rng1
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/program-max-bits/bits-1023/refs-{refs}" #[] 1023 refs, rng2)
  else if shape = 5 then
    let (noise, rng2) := pickNoiseValue rng1
    let (bits, rng3) := pickBitsMixed rng2
    let (refs, rng4) := pickRefsMixed rng3
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/deep1/bits-{bits}/refs-{refs}" #[noise] bits refs, rng4)
  else if shape = 6 then
    let (noise1, rng2) := pickNoiseValue rng1
    let (noise2, rng3) := pickNoiseValue rng2
    let (bits, rng4) := pickBitsMixed rng3
    let (refs, rng5) := pickRefsMixed rng4
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/deep2/bits-{bits}/refs-{refs}" #[noise1, noise2] bits refs, rng5)
  else if shape = 7 then
    let (refs, rng2) := randNat rng1 1 4
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/refs-only/refs-{refs}" #[] 0 refs, rng2)
  else if shape = 8 then
    let (bits, rng2) := pickBitsMixed rng1
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/bits-only/bits-{bits}" #[] bits 0, rng2)
  else if shape = 9 then
    (mkBbitrefsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 10 then
    (mkBbitrefsCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 11 then
    let (n, rng2) := randNat rng1 0 255
    (mkBbitrefsCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
  else if shape = 12 then
    (mkBbitrefsCase "fuzz/type/top-cell" #[.cell refCellC], rng1)
  else if shape = 13 then
    (mkBbitrefsCase "fuzz/type/top-slice-full" #[.slice fullSliceNoiseA], rng1)
  else if shape = 14 then
    (mkBbitrefsCase "fuzz/type/top-tuple-empty" #[.tuple #[]], rng1)
  else if shape = 15 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkBbitrefsCase "fuzz/type/deep-top-not-builder" #[.builder Builder.empty, noise], rng2)
  else if shape = 16 then
    (mkBbitrefsCase "fuzz/gas/exact"
      #[.builder Builder.empty]
      #[.pushInt (.num bbitrefsSetGasExact), .tonEnvOp .setGasLimit, bbitrefsInstr], rng1)
  else if shape = 17 then
    (mkBbitrefsCase "fuzz/gas/exact-minus-one"
      #[.builder Builder.empty]
      #[.pushInt (.num bbitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bbitrefsInstr], rng1)
  else if shape = 18 then
    let (bits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBbitrefsSizedProgramCase s!"fuzz/ok/full-slice-noise/bits-{bits}/refs-{refs}"
      #[.slice fullSliceNoiseB] bits refs, rng3)
  else if shape = 19 then
    (mkBbitrefsSizedProgramCase "fuzz/ok/fixed-256-refs4" #[] 256 4, rng1)
  else
    (mkBbitrefsSizedProgramCase "fuzz/ok/fixed-1023-refs4" #[.null] 1023 4, rng1)

def suite : InstrSuite where
  id := bbitrefsId
  unit := #[
    { name := "unit/direct/success-order-and-boundaries"
      run := do
        expectOkStack "ok/empty-builder"
          (runBbitrefsDirect #[.builder builderEmpty])
          (expectedBbitrefsOut #[] builderEmpty)

        expectOkStack "ok/bits9-refs0"
          (runBbitrefsDirect #[.builder builderBits9Refs0])
          (expectedBbitrefsOut #[] builderBits9Refs0)

        expectOkStack "ok/bits0-refs3"
          (runBbitrefsDirect #[.builder builderBits0Refs3])
          (expectedBbitrefsOut #[] builderBits0Refs3)

        expectOkStack "ok/bits17-refs2"
          (runBbitrefsDirect #[.builder builderBits17Refs2])
          (expectedBbitrefsOut #[] builderBits17Refs2)

        expectOkStack "ok/bits257-refs1"
          (runBbitrefsDirect #[.builder builderBits257Refs1])
          (expectedBbitrefsOut #[] builderBits257Refs1)

        expectOkStack "ok/bits1023-refs4"
          (runBbitrefsDirect #[.builder builderBits1023Refs4])
          (expectedBbitrefsOut #[] builderBits1023Refs4)

        expectOkStack "ok/deep-stack-order-preserved"
          (runBbitrefsDirect #[.null, intV 91, .builder builderBits17Refs2])
          (expectedBbitrefsOut #[.null, intV 91] builderBits17Refs2) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runBbitrefsDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runBbitrefsDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runBbitrefsDirect #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runBbitrefsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice-full"
          (runBbitrefsDirect #[.slice fullSliceNoiseA]) .typeChk
        expectErr "type/top-tuple-empty"
          (runBbitrefsDirect #[.tuple #[]]) .typeChk

        expectErr "type/deep-top-not-builder"
          (runBbitrefsDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-bbitrefs"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBbitrefsDirect #[.builder builderBits17Refs2]),
            ("underflow", runBbitrefsDirect #[]),
            ("type", runBbitrefsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BBITREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [bbitrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble bbitrefs failed: {e}")
        if single.bits = natToBits bbitrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"bbitrefs canonical encode mismatch: got bits {single.bits}")

        let program : Array Instr := #[.cellOp .brefs, bbitrefsInstr, .cellOp .brembits, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/brefs" s0 (.cellOp .brefs) 16
        let s2 ← expectDecodeStep "decode/bbitrefs" s1 bbitrefsInstr 16
        let s3 ← expectDecodeStep "decode/brembits" s2 (.cellOp .brembits) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xcf31 16 ++
            natToBits 0xcf32 16 ++
            natToBits 0xcf33 16 ++
            natToBits 0xcf35 16 ++
            addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xcf31-bbits" r0 .bbits 16
        let r2 ← expectDecodeStep "decode/raw-0xcf32-brefs" r1 (.cellOp .brefs) 16
        let r3 ← expectDecodeStep "decode/raw-0xcf33-bbitrefs" r2 bbitrefsInstr 16
        let r4 ← expectDecodeStep "decode/raw-0xcf35-brembits" r3 (.cellOp .brembits) 16
        let r5 ← expectDecodeStep "decode/raw-tail-add" r4 .add 8
        if r5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r5.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/fallback"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runBbitrefsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-bbits"
          (runBbitrefsDispatchFallback .bbits #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-brefs"
          (runBbitrefsDispatchFallback (.cellOp .brefs) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-brembits"
          (runBbitrefsDispatchFallback (.cellOp .brembits) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
  ]
  oracle := #[
    mkBbitrefsCase "ok/direct-empty-builder"
      #[.builder Builder.empty],

    mkBbitrefsSizedProgramCase "ok/program/bits1-refs0"
      #[] 1 0,
    mkBbitrefsSizedProgramCase "ok/program/bits7-refs1"
      #[] 7 1,
    mkBbitrefsSizedProgramCase "ok/program/bits8-refs2"
      #[] 8 2,
    mkBbitrefsSizedProgramCase "ok/program/bits15-refs3"
      #[] 15 3,
    mkBbitrefsSizedProgramCase "ok/program/bits31-refs4"
      #[] 31 4,
    mkBbitrefsSizedProgramCase "ok/program/bits63-refs0"
      #[] 63 0,
    mkBbitrefsSizedProgramCase "ok/program/bits127-refs2"
      #[] 127 2,
    mkBbitrefsSizedProgramCase "ok/program/bits256-refs1"
      #[] 256 1,
    mkBbitrefsSizedProgramCase "ok/program/bits511-refs4"
      #[] 511 4,
    mkBbitrefsSizedProgramCase "ok/program/bits768-refs3"
      #[] 768 3,
    mkBbitrefsSizedProgramCase "ok/program/bits1023-refs4"
      #[] 1023 4,
    mkBbitrefsSizedProgramCase "ok/program/deep-null/bits9-refs1"
      #[.null] 9 1,
    mkBbitrefsSizedProgramCase "ok/program/deep-int-cell/bits33-refs2"
      #[intV (-9), .cell refCellA] 33 2,
    mkBbitrefsSizedProgramCase "ok/program/deep-slice-tuple/bits5-refs3"
      #[.slice fullSliceNoiseB, .tuple #[]] 5 3,

    mkBbitrefsCase "underflow/empty"
      #[],
    mkBbitrefsCase "type/top-null"
      #[.null],
    mkBbitrefsCase "type/top-int"
      #[intV 12],
    mkBbitrefsCase "type/top-cell"
      #[.cell refCellC],
    mkBbitrefsCase "type/top-slice-full"
      #[.slice fullSliceNoiseA],
    mkBbitrefsCase "type/top-tuple-empty"
      #[.tuple #[]],
    mkBbitrefsCase "type/deep-top-not-builder-builder-below"
      #[.builder Builder.empty, .null],

    mkBbitrefsCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num bbitrefsSetGasExact), .tonEnvOp .setGasLimit, bbitrefsInstr],
    mkBbitrefsCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num bbitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, bbitrefsInstr]
  ]
  fuzz := #[
    { seed := 2026021086
      count := 500
      gen := genBbitrefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BBITREFS
