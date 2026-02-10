import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.BREMBITS

/-
BREMBITS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Brembits.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch chain for `.cellOp`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`BREMBITS` encode `0xcf35`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xcf35` decode to `.cellOp .brembits`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_int_builder_func`, `BREMBITS`: remaining data bits).

Branch contracts covered here:
- dispatch: `.cellOp .brembits` arm vs `next` passthrough;
- stack behavior: `popBuilder` yields `stkUnd` on empty stack, `typeChk` on non-builder top;
- success path: pushes exactly one small-int equal to `1023 - builder.bits.size`, refs ignored;
- decode/assembler boundaries: exact `0xcf35`, neighboring `0xcf3x` family, and `0xcf34` gap.

Harness note:
- oracle stack tokens support empty builders only; non-empty builders for oracle/fuzz are
  created in-program via `NEWC` + `STU` (+ optional `STREF`).
- all oracle/fuzz slice values are full-cell slices (`bitPos = 0`, `refPos = 0`).
-/

private def brembitsId : InstrId := { name := "BREMBITS" }

private def brembitsInstr : Instr := .cellOp .brembits

private def brembitsOpcode : Nat := 0xcf35

private def dispatchSentinel : Int := 735

private def execInstrCellOpBrembitsOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpBrembits op next
  | _ => next

private def mkBrembitsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[brembitsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := brembitsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPatternBits (bitCount : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := bitCount) fun i => ((i.1 + phase) % 3 = 1) || ((i.1 + phase) % 5 = 0)

private def mkBuilderWith
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Builder :=
  { bits := mkPatternBits bitCount phase, refs := refs }

private def mkFullSlice
    (bitCount : Nat)
    (phase : Nat := 0)
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkPatternBits bitCount phase) refs)

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 11 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 21 5) #[]

private def refLeafD : Cell :=
  Cell.mkOrdinary (natToBits 42 6) #[]

private def refPool : Array Cell :=
  #[refLeafA, refLeafB, refLeafC, refLeafD]

private def takeRefCells (n : Nat) : Array Cell :=
  refPool.extract 0 (Nat.min n refPool.size)

private def cellsToStack (cells : Array Cell) : Array Value :=
  cells.map (fun c => .cell c)

private def stuChunks (bitCount : Nat) : Array Nat :=
  let fullChunks := Array.replicate (bitCount / 256) 256
  let rem := bitCount % 256
  if rem = 0 then
    fullChunks
  else
    fullChunks.push rem

private def buildBuilderProgram (bitCount : Nat) (refCount : Nat := 0) : Array Instr := Id.run do
  let mut program : Array Instr := #[.newc]
  for chunk in stuChunks bitCount do
    program := program ++ #[.pushInt (.num 0), .xchg0 1, .stu chunk]
  for _ in [0:refCount] do
    program := program.push .stref
  program := program.push brembitsInstr
  return program

private def mkBrembitsBuildCase
    (name : String)
    (bitCount : Nat)
    (refCount : Nat := 0)
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let refs := takeRefCells refCount
  let stack := below ++ cellsToStack refs
  mkBrembitsCase name stack (buildBuilderProgram bitCount refCount) gasLimits fuel

private def runBrembitsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpBrembitsOnly brembitsInstr stack

private def runBrembitsDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpBrembitsOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def bchkBitsImmWord (bits : Nat) (quiet : Bool) : Nat :=
  let base : Nat := if quiet then 0xcf3c else 0xcf38
  (base <<< 8) + (bits - 1)

private def brembitsSetGasExact : Int :=
  computeExactGasBudget brembitsInstr

private def brembitsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne brembitsInstr

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 257, 511, 512, 767, 1022, 1023]

private def pickBitsBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (bitsBoundaryPool.size - 1)
  (bitsBoundaryPool[idx]!, rng')

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickBitsBoundary rng1
  else
    randNat rng1 0 1023

private def pickNoiseValue (rng : StdGen) : Value × String × StdGen :=
  let (pick, rng') := randNat rng 0 4
  let out : Value × String :=
    if pick = 0 then
      (.null, "null")
    else if pick = 1 then
      (intV 91, "int")
    else if pick = 2 then
      (.cell refLeafA, "cell")
    else if pick = 3 then
      (.slice (mkFullSlice 9 1), "slice")
    else
      (.builder Builder.empty, "builder")
  (out.1, out.2, rng')

private def pickBadTopValue (rng : StdGen) : Value × String × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let out : Value × String :=
    if pick = 0 then
      (.null, "null")
    else if pick = 1 then
      (intV 17, "int")
    else if pick = 2 then
      (.cell refLeafB, "cell")
    else
      (.slice (mkFullSlice 12 2), "slice")
  (out.1, out.2, rng')

private def genBrembitsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (case0, rng2) :=
    if shape = 0 then
      let (bits, rng2) := pickBitsMixed rng1
      (mkBrembitsBuildCase s!"fuzz/ok/program/bits-{bits}" bits, rng2)
    else if shape = 1 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := randNat rng2 1 4
      (mkBrembitsBuildCase s!"fuzz/ok/program/bits-{bits}/refs-{refs}" bits refs, rng3)
    else if shape = 2 then
      let (bits, rng2) := pickBitsBoundary rng1
      (mkBrembitsBuildCase s!"fuzz/ok/program/boundary-bits-{bits}" bits, rng2)
    else if shape = 3 then
      let (refs, rng2) := randNat rng1 1 4
      (mkBrembitsBuildCase s!"fuzz/ok/program/refs-only-{refs}" 0 refs, rng2)
    else if shape = 4 then
      (mkBrembitsCase "fuzz/ok/direct/empty-builder" #[.builder Builder.empty], rng1)
    else if shape = 5 then
      let (noise, tag, rng2) := pickNoiseValue rng1
      (mkBrembitsCase s!"fuzz/ok/direct/deep-{tag}" #[noise, .builder Builder.empty], rng2)
    else if shape = 6 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := randNat rng2 0 4
      let (noise, tag, rng4) := pickNoiseValue rng3
      (mkBrembitsBuildCase s!"fuzz/ok/program/deep-{tag}/bits-{bits}/refs-{refs}" bits refs #[noise], rng4)
    else if shape = 7 then
      (mkBrembitsCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 8 then
      let (bad, badTag, rng2) := pickBadTopValue rng1
      (mkBrembitsCase s!"fuzz/type/top-not-builder-{badTag}" #[bad], rng2)
    else if shape = 9 then
      let (bad, badTag, rng2) := pickBadTopValue rng1
      (mkBrembitsCase s!"fuzz/type/order-top-{badTag}-over-builder" #[.builder Builder.empty, bad], rng2)
    else if shape = 10 then
      (mkBrembitsCase "fuzz/gas/exact"
        #[.builder Builder.empty]
        #[.pushInt (.num brembitsSetGasExact), .tonEnvOp .setGasLimit, brembitsInstr], rng1)
    else if shape = 11 then
      (mkBrembitsCase "fuzz/gas/exact-minus-one"
        #[.builder Builder.empty]
        #[.pushInt (.num brembitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brembitsInstr], rng1)
    else
      let (noise, tag, rng2) := pickNoiseValue rng1
      (mkBrembitsBuildCase s!"fuzz/stress/max/deep-{tag}" 1023 4 #[noise], rng2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleDirectCases : Array OracleCase :=
  #[
    mkBrembitsCase "ok/direct-empty-builder" #[.builder Builder.empty],
    mkBrembitsCase "ok/direct-deep-null" #[.null, .builder Builder.empty],
    mkBrembitsCase "ok/direct-deep-full-slice" #[.slice (mkFullSlice 9 1), .builder Builder.empty]
  ]

private def oracleProgramBitsCases : Array OracleCase :=
  #[0, 1, 7, 8, 15, 16, 255, 256, 1022, 1023].map (fun bits =>
    mkBrembitsBuildCase s!"ok/program-bits-{bits}" bits)

private def oracleProgramRefCases : Array OracleCase :=
  #[
    mkBrembitsBuildCase "ok/program-refs-only-1" 0 1,
    mkBrembitsBuildCase "ok/program-refs-only-4" 0 4,
    mkBrembitsBuildCase "ok/program-bits-32-refs-2" 32 2,
    mkBrembitsBuildCase "ok/program-bits-256-refs-4-deep-slice" 256 4 #[.slice (mkFullSlice 6 0)]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkBrembitsCase "underflow/empty" #[],
    mkBrembitsCase "type/top-null" #[.null],
    mkBrembitsCase "type/top-int" #[intV 3],
    mkBrembitsCase "type/top-cell" #[.cell refLeafB],
    mkBrembitsCase "error-order/top-null-over-builder" #[.builder Builder.empty, .null]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkBrembitsCase "gas/exact-cost-succeeds"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitsSetGasExact), .tonEnvOp .setGasLimit, brembitsInstr],
    mkBrembitsCase "gas/exact-minus-one-out-of-gas"
      #[.builder Builder.empty]
      #[.pushInt (.num brembitsSetGasExactMinusOne), .tonEnvOp .setGasLimit, brembitsInstr]
  ]

def suite : InstrSuite where
  id := { name := "BREMBITS" }
  unit := #[
    { name := "unit/direct/rembits-success-boundaries-and-refs-ignored"
      run := do
        let builders : Array Builder :=
          #[
            Builder.empty,
            mkBuilderWith 1 0,
            mkBuilderWith 8 1 (takeRefCells 2),
            mkBuilderWith 16 2 (takeRefCells 1),
            mkBuilderWith 255 3 (takeRefCells 4),
            mkBuilderWith 256 1,
            mkBuilderWith 511 2 (takeRefCells 3),
            mkBuilderWith 1022 0 (takeRefCells 1),
            mkBuilderWith 1023 4 (takeRefCells 4)
          ]
        for i in [0:builders.size] do
          let b ←
            match builders[i]? with
            | some b => pure b
            | none => throw (IO.userError s!"builders index out of bounds: {i}")
          let expected := intV (Int.ofNat (1023 - b.bits.size))
          expectOkStack s!"ok/case-{i}/bits-{b.bits.size}/refs-{b.refs.size}"
            (runBrembitsDirect #[.builder b])
            #[expected]

        let below : Array Value := #[.slice (mkFullSlice 9 1), intV 77]
        let deepBuilder := mkBuilderWith 32 3 (takeRefCells 2)
        expectOkStack "ok/deep-stack-preserve-below"
          (runBrembitsDirect (below ++ #[.builder deepBuilder]))
          (below ++ #[intV (Int.ofNat (1023 - 32))]) }
    ,
    { name := "unit/direct/pop-order-top-builder-controls-result"
      run := do
        let low := mkBuilderWith 5 0 (takeRefCells 1)
        let high := mkBuilderWith 37 2 (takeRefCells 3)
        expectOkStack "order/two-builders-pop-top"
          (runBrembitsDirect #[.builder low, .builder high])
          #[.builder low, intV (Int.ofNat (1023 - 37))]

        let below : Array Value := #[.cell refLeafA, .slice (mkFullSlice 8 0)]
        let top := mkBuilderWith 255 1
        expectOkStack "order/deep-stack-only-top-builder-popped"
          (runBrembitsDirect (below ++ #[.builder top]))
          (below ++ #[intV (Int.ofNat (1023 - 255))]) }
    ,
    { name := "unit/direct/underflow-type-and-error-order"
      run := do
        expectErr "underflow/empty" (runBrembitsDirect #[]) .stkUnd
        expectErr "type/top-null" (runBrembitsDirect #[.null]) .typeChk
        expectErr "type/top-int" (runBrembitsDirect #[intV 1]) .typeChk
        expectErr "type/top-cell" (runBrembitsDirect #[.cell refLeafA]) .typeChk
        expectErr "type/top-full-slice" (runBrembitsDirect #[.slice (mkFullSlice 7 2)]) .typeChk
        expectErr "error-order/top-not-builder-over-builder"
          (runBrembitsDirect #[.builder Builder.empty, .null]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-brembits"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runBrembitsDirect #[.builder (mkBuilderWith 32 1)]),
            ("underflow", runBrembitsDirect #[]),
            ("type", runBrembitsDirect #[.null])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for BREMBITS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-boundary-and-gap"
      run := do
        let familyProgram : Array Instr := #[
          .cellOp .bdepth,
          .bbits,
          .cellOp .brefs,
          .cellOp .bbitrefs,
          brembitsInstr,
          .cellOp .bremrefs,
          .cellOp .brembitrefs,
          .add
        ]
        let familyCode ←
          match assembleCp0 familyProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let f0 := Slice.ofCell familyCode
        let f1 ← expectDecodeStep "decode/bdepth" f0 (.cellOp .bdepth) 16
        let f2 ← expectDecodeStep "decode/bbits" f1 .bbits 16
        let f3 ← expectDecodeStep "decode/brefs" f2 (.cellOp .brefs) 16
        let f4 ← expectDecodeStep "decode/bbitrefs" f3 (.cellOp .bbitrefs) 16
        let f5 ← expectDecodeStep "decode/brembits" f4 brembitsInstr 16
        let f6 ← expectDecodeStep "decode/bremrefs" f5 (.cellOp .bremrefs) 16
        let f7 ← expectDecodeStep "decode/brembitrefs" f6 (.cellOp .brembitrefs) 16
        let f8 ← expectDecodeStep "decode/tail-add" f7 .add 8
        if f8.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/family-end: expected exhausted slice, got {f8.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [brembitsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits brembitsOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/brembits: expected 0xcf35 encoding, got bits {singleCode.bits}")
        if singleCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/brembits: expected 16-bit encoding, got {singleCode.bits.size}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits brembitsOpcode 16 ++ natToBits (bchkBitsImmWord 1 false) 24 ++ addCell.bits) #[]
        let r0 := Slice.ofCell rawBoundary
        let r1 ← expectDecodeStep "decode/raw-brembits" r0 brembitsInstr 16
        let r2 ← expectDecodeStep "decode/raw-bchkbits-imm1" r1 (.cellOp (.bchkBitsImm 1 false)) 24
        let r3 ← expectDecodeStep "decode/raw-tail-add" r2 .add 8
        if r3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r3.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-cf34"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xcf34 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-brembits-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runBrembitsDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/bbits"
          (runBrembitsDispatchFallback .bbits #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-brefs"
          (runBrembitsDispatchFallback (.cellOp .brefs) #[.builder Builder.empty])
          #[.builder Builder.empty, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-bremrefs"
          (runBrembitsDispatchFallback (.cellOp .bremrefs) #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel] }
  ]
  oracle := oracleDirectCases ++ oracleProgramBitsCases ++ oracleProgramRefCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021093
      count := 320
      gen := genBrembitsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.BREMBITS
