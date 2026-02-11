import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BREMBITREFS

/-
BREMBITREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Brembitrefs.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xcf37` encode)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf37` decode to `.cellOp .brembitrefs`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_2int_builder_func`, opcode registration `0xcf37`, pushes remaining `(bits, refs)`).

Covered branches:
- dispatch guard (`.cellOp .brembitrefs` arm vs `next`);
- `popBuilder` underflow/type failures;
- success contract and order:
  `... builder -> ... remBits remRefs` with `remBits = 1023 - bits.size`, `remRefs = 4 - refs.size`;
- decode/assembler boundaries around `0xcf37` and neighboring `0xcf3x` opcodes.

Harness note:
- oracle stack tokens cannot encode non-empty builders directly; oracle/fuzz success
  cases construct non-empty builders in `program` using `NEWC` + `STU` + `STREF`.
-/

private def brembitrefsId : InstrId := { name := "BREMBITREFS" }

private def brembitrefsInstr : Instr := .cellOp .brembitrefs

private def brembitrefsWord : Nat := 0xcf37

private def dispatchSentinel : Int := 5371

private def execInstrCellOpBrembitrefsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBrembitrefs op next
  | _ => next

private def mkBrembitrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[brembitrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := brembitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkBrembitrefsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := brembitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runBrembitrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBrembitrefsOnly brembitrefsInstr stack

private def runBrembitrefsDispatchWithNext (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBrembitrefsOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def brembitrefsSetGasExact : Int :=
  computeExactGasBudget brembitrefsInstr

private def brembitrefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne brembitrefsInstr

private def patternBits (n : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := n) fun i => ((i.1 + phase) % 2 = 1) || ((i.1 + phase) % 5 = 0)

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
  { bits := patternBits bitCount phase, refs := mkRefArray refCount }

private def builderEmpty : Builder :=
  Builder.empty

private def builderBits9Refs0 : Builder :=
  mkBuilderWithSizes 9 0

private def builderBits0Refs3 : Builder :=
  mkBuilderWithSizes 0 3

private def builderBits17Refs2 : Builder :=
  mkBuilderWithSizes 17 2 1

private def builderBits257Refs1 : Builder :=
  mkBuilderWithSizes 257 1 2

private def builderBits1023Refs4 : Builder :=
  mkBuilderWithSizes 1023 4 3

private def builderBits1024Refs0 : Builder :=
  mkBuilderWithSizes 1024 0

private def builderBits2000Refs5 : Builder :=
  mkBuilderWithSizes 2000 5 1

private def builderBits0Refs6 : Builder :=
  mkBuilderWithSizes 0 6

private def fullSliceNoiseA : Slice :=
  Slice.ofCell (Cell.mkOrdinary (patternBits 7 1) #[refCellA])

private def fullSliceNoiseB : Slice :=
  Slice.ofCell (Cell.mkOrdinary #[] #[refCellB, refCellC])

private def expectedBrembitrefsOut (below : Array Value) (b : Builder) : Array Value :=
  below ++ #[intV (Int.ofNat (1023 - b.bits.size)), intV (Int.ofNat (4 - b.refs.size))]

private def mkBuilderProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  #[.newc] ++ appendBitsToTopBuilder bits x ++ appendRefsToTopBuilder refs

private def mkBrembitrefsProgram
    (bits : Nat)
    (refs : Nat)
    (x : IntVal := .num 0) : Array Instr :=
  mkBuilderProgram bits refs x ++ #[brembitrefsInstr]

private def mkBrembitrefsSizedProgramCase
    (name : String)
    (below : Array Value)
    (bits refs : Nat) : OracleCase :=
  mkBrembitrefsProgramCase name below (mkBrembitrefsProgram bits refs)

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

private def genBrembitrefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  if shape = 0 then
    (mkBrembitrefsCase "fuzz/ok/direct-empty-builder" #[.builder Builder.empty], rng1)
  else if shape = 1 then
    let (bits, rng2) := pickBitsBoundary rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/program-boundary/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 2 then
    let (bits, rng2) := randNat rng1 0 128
    let (refs, rng3) := pickRefsMixed rng2
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/program-small/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 3 then
    let (bits, rng2) := randNat rng1 257 1023
    let (refs, rng3) := pickRefsMixed rng2
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/program-high/bits-{bits}/refs-{refs}" #[] bits refs, rng3)
  else if shape = 4 then
    let (refs, rng2) := pickRefsMixed rng1
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/program-max-bits/bits-1023/refs-{refs}" #[] 1023 refs, rng2)
  else if shape = 5 then
    let (noise, rng2) := pickNoiseValue rng1
    let (bits, rng3) := pickBitsMixed rng2
    let (refs, rng4) := pickRefsMixed rng3
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/deep1/bits-{bits}/refs-{refs}" #[noise] bits refs, rng4)
  else if shape = 6 then
    let (noise1, rng2) := pickNoiseValue rng1
    let (noise2, rng3) := pickNoiseValue rng2
    let (bits, rng4) := pickBitsMixed rng3
    let (refs, rng5) := pickRefsMixed rng4
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/deep2/bits-{bits}/refs-{refs}" #[noise1, noise2] bits refs, rng5)
  else if shape = 7 then
    let (refs, rng2) := randNat rng1 1 4
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/refs-only/refs-{refs}" #[] 0 refs, rng2)
  else if shape = 8 then
    let (bits, rng2) := pickBitsMixed rng1
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/bits-only/bits-{bits}" #[] bits 0, rng2)
  else if shape = 9 then
    (mkBrembitrefsCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 10 then
    (mkBrembitrefsCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 11 then
    let (n, rng2) := randNat rng1 0 255
    (mkBrembitrefsCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
  else if shape = 12 then
    (mkBrembitrefsCase "fuzz/type/top-cell" #[.cell refCellC], rng1)
  else if shape = 13 then
    (mkBrembitrefsCase "fuzz/type/top-slice-full" #[.slice fullSliceNoiseA], rng1)
  else if shape = 14 then
    (mkBrembitrefsCase "fuzz/type/top-tuple-empty" #[.tuple #[]], rng1)
  else if shape = 15 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkBrembitrefsCase "fuzz/type/deep-top-not-builder" #[.builder Builder.empty, noise], rng2)
  else if shape = 16 then
    (mkBrembitrefsCase "fuzz/gas/exact"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitrefsSetGasExact), .tonEnvOp .setGasLimit, brembitrefsInstr], rng1)
  else if shape = 17 then
    (mkBrembitrefsCase "fuzz/gas/exact-minus-one"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brembitrefsInstr], rng1)
  else if shape = 18 then
    let (bits, rng2) := pickBitsMixed rng1
    let (refs, rng3) := pickRefsMixed rng2
    (mkBrembitrefsSizedProgramCase s!"fuzz/ok/full-slice-noise/bits-{bits}/refs-{refs}"
      #[.slice fullSliceNoiseB] bits refs, rng3)
  else if shape = 19 then
    (mkBrembitrefsSizedProgramCase "fuzz/ok/fixed-256-refs4" #[] 256 4, rng1)
  else
    (mkBrembitrefsSizedProgramCase "fuzz/ok/fixed-1023-refs4" #[.null] 1023 4, rng1)

def suite : InstrSuite where
  id := brembitrefsId
  unit := #[
    { name := "unit/direct/success-order-and-boundaries"
      run := do
        expectOkStack "ok/empty-builder"
          (runBrembitrefsDirect #[.builder builderEmpty])
          (expectedBrembitrefsOut #[] builderEmpty)

        expectOkStack "ok/bits9-refs0"
          (runBrembitrefsDirect #[.builder builderBits9Refs0])
          (expectedBrembitrefsOut #[] builderBits9Refs0)

        expectOkStack "ok/bits0-refs3"
          (runBrembitrefsDirect #[.builder builderBits0Refs3])
          (expectedBrembitrefsOut #[] builderBits0Refs3)

        expectOkStack "ok/bits17-refs2"
          (runBrembitrefsDirect #[.builder builderBits17Refs2])
          (expectedBrembitrefsOut #[] builderBits17Refs2)

        expectOkStack "ok/bits257-refs1"
          (runBrembitrefsDirect #[.builder builderBits257Refs1])
          (expectedBrembitrefsOut #[] builderBits257Refs1)

        expectOkStack "ok/bits1023-refs4"
          (runBrembitrefsDirect #[.builder builderBits1023Refs4])
          (expectedBrembitrefsOut #[] builderBits1023Refs4)

        expectOkStack "ok/deep-stack-order-preserved"
          (runBrembitrefsDirect #[.null, intV 91, .builder builderBits17Refs2])
          (expectedBrembitrefsOut #[.null, intV 91] builderBits17Refs2)

        expectOkStack "ok/two-builders-only-top-consumed"
          (runBrembitrefsDirect #[.builder builderBits9Refs0, .builder builderBits0Refs3])
          #[.builder builderBits9Refs0, intV 1023, intV 1] }
    ,
    { name := "unit/direct/oversized-builder-saturates-at-zero"
      run := do
        expectOkStack "ok/over-bits-1024-refs0"
          (runBrembitrefsDirect #[.builder builderBits1024Refs0])
          (expectedBrembitrefsOut #[] builderBits1024Refs0)

        expectOkStack "ok/over-bits-2000-refs5"
          (runBrembitrefsDirect #[.builder builderBits2000Refs5])
          (expectedBrembitrefsOut #[] builderBits2000Refs5)

        expectOkStack "ok/over-refs-6-only"
          (runBrembitrefsDirect #[.builder builderBits0Refs6])
          (expectedBrembitrefsOut #[] builderBits0Refs6)

        expectOkStack "ok/deep-overflowed-builder-preserves-below"
          (runBrembitrefsDirect #[.slice fullSliceNoiseA, intV (-9), .builder builderBits2000Refs5])
          (expectedBrembitrefsOut #[.slice fullSliceNoiseA, intV (-9)] builderBits2000Refs5) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runBrembitrefsDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runBrembitrefsDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runBrembitrefsDirect #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runBrembitrefsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice-full"
          (runBrembitrefsDirect #[.slice fullSliceNoiseA]) .typeChk
        expectErr "type/top-tuple-empty"
          (runBrembitrefsDirect #[.tuple #[]]) .typeChk

        expectErr "type/deep-top-not-builder"
          (runBrembitrefsDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-brembitrefs"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBrembitrefsDirect #[.builder builderBits17Refs2]),
            ("success-oversized", runBrembitrefsDirect #[.builder builderBits2000Refs5]),
            ("underflow", runBrembitrefsDirect #[]),
            ("type", runBrembitrefsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BREMBITREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-and-assembler-boundary"
      run := do
        let single ←
          match assembleCp0 [brembitrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble brembitrefs failed: {e}")
        if single.bits = natToBits brembitrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"brembitrefs canonical encode mismatch: got bits {single.bits}")
        if single.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"brembitrefs encode width mismatch: got {single.bits.size} bits")

        let program : Array Instr :=
          #[.cellOp .brembits, .cellOp .bremrefs, brembitrefsInstr, .cellOp (.bchk true false false), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/brembits" s0 (.cellOp .brembits) 16
        let s2 ← expectDecodeStep "decode/bremrefs" s1 (.cellOp .bremrefs) 16
        let s3 ← expectDecodeStep "decode/brembitrefs" s2 brembitrefsInstr 16
        let s4 ← expectDecodeStep "decode/bchk-var-bits" s3 (.cellOp (.bchk true false false)) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xcf36 16 ++
            natToBits 0xcf37 16 ++
            natToBits 0xcf39 16 ++
            addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xcf36-bremrefs" r0 (.cellOp .bremrefs) 16
        let r2 ← expectDecodeStep "decode/raw-0xcf37-brembitrefs" r1 brembitrefsInstr 16
        let r3 ← expectDecodeStep "decode/raw-0xcf39-bchk-var-bits" r2 (.cellOp (.bchk true false false)) 16
        let r4 ← expectDecodeStep "decode/raw-tail-add" r3 .add 8
        if r4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r4.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-cf34"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xcf34 16) #[]))
          .invOpcode
        expectDecodeErr "decode/raw-bchkbits-imm-missing-arg-cf38"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xcf38 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-handled"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runBrembitrefsDispatchWithNext .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bremrefs"
          (runBrembitrefsDispatchWithNext (.cellOp .bremrefs) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-bbitrefs"
          (runBrembitrefsDispatchWithNext (.cellOp .bbitrefs) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel]

        expectOkStack "dispatch/handled-brembitrefs-does-not-run-next"
          (runBrembitrefsDispatchWithNext brembitrefsInstr #[.builder builderBits17Refs2])
          #[intV 1006, intV 2] }
  ]
  oracle := #[
    mkBrembitrefsCase "ok/direct-empty-builder"
      #[.builder Builder.empty],

    mkBrembitrefsSizedProgramCase "ok/program/bits0-refs0"
      #[] 0 0,
    mkBrembitrefsSizedProgramCase "ok/program/bits1-refs0"
      #[] 1 0,
    mkBrembitrefsSizedProgramCase "ok/program/bits0-refs1"
      #[] 0 1,
    mkBrembitrefsSizedProgramCase "ok/program/bits8-refs2"
      #[] 8 2,
    mkBrembitrefsSizedProgramCase "ok/program/bits15-refs3"
      #[] 15 3,
    mkBrembitrefsSizedProgramCase "ok/program/bits31-refs4"
      #[] 31 4,
    mkBrembitrefsSizedProgramCase "ok/program/bits63-refs0"
      #[] 63 0,
    mkBrembitrefsSizedProgramCase "ok/program/bits127-refs2"
      #[] 127 2,
    mkBrembitrefsSizedProgramCase "ok/program/bits256-refs1"
      #[] 256 1,
    mkBrembitrefsSizedProgramCase "ok/program/bits511-refs4"
      #[] 511 4,
    mkBrembitrefsSizedProgramCase "ok/program/bits1023-refs4"
      #[] 1023 4,
    mkBrembitrefsSizedProgramCase "ok/program/deep-null/bits9-refs1"
      #[.null] 9 1,
    mkBrembitrefsSizedProgramCase "ok/program/deep-int-cell/bits33-refs2"
      #[intV (-9), .cell refCellA] 33 2,
    mkBrembitrefsSizedProgramCase "ok/program/deep-slice-tuple/bits5-refs3"
      #[.slice fullSliceNoiseB, .tuple #[]] 5 3,

    mkBrembitrefsCase "underflow/empty"
      #[],
    mkBrembitrefsCase "type/top-null"
      #[.null],
    mkBrembitrefsCase "type/top-int"
      #[intV 12],
    mkBrembitrefsCase "type/top-cell"
      #[.cell refCellC],
    mkBrembitrefsCase "type/top-slice-full"
      #[.slice fullSliceNoiseA],
    mkBrembitrefsCase "type/top-tuple-empty"
      #[.tuple #[]],
    mkBrembitrefsCase "type/deep-top-not-builder-builder-below"
      #[.builder Builder.empty, .null],

    mkBrembitrefsCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitrefsSetGasExact), .tonEnvOp .setGasLimit, brembitrefsInstr],
    mkBrembitrefsCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brembitrefsInstr]
  ]
  fuzz := #[
    { seed := 2026021097
      count := 500
      gen := genBrembitrefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BREMBITREFS
