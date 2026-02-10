import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SBITREFS

/-!
SBITREFS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sbitrefs.lean`
  - `TvmLean/Semantics/Exec/Cell.lean` (cell-dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.sbitrefs` encodes to `0xd74b`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd74b` decodes to `.sbitrefs`)
- C++ authority:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (slice-size op family covering `SBITS`/`SREFS`/`SBITREFS`).

Covered branches:
- dispatch guard (`.sbitrefs` handled vs `next`);
- `popSlice` paths: underflow and strict top-type checks;
- success contract and push order:
  `... slice -> ... bitsRemaining refsRemaining` (refs on top);
- decode/assembler boundaries around `0xd74b` and immediate neighbors.
-/

private def sbitrefsId : InstrId := { name := "SBITREFS" }

private def sbitrefsInstr : Instr := .sbitrefs

private def sbitrefsWord : Nat := 0xd74b

private def dispatchSentinel : Int := 7431

private def execInstrCellSbitrefsOnly (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrCellSbitrefs i next

private def mkSbitrefsCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sbitrefsInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSbitrefsProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sbitrefsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSbitrefsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSbitrefsOnly sbitrefsInstr stack

private def runSbitrefsDispatchWithNext (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSbitrefsOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def sbitrefsSetGasExact : Int :=
  computeExactGasBudget sbitrefsInstr

private def sbitrefsSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sbitrefsInstr

private def patternBits (n : Nat) (phase : Nat := 0) : BitString := Id.run do
  let mut out : BitString := #[]
  for i in [0:n] do
    let bit := ((i + phase) % 2 == 0) || ((i + phase) % 5 == 3)
    out := out.push bit
  return out

private def mkCellWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary bits refs

private def mkSliceWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs bits refs)

private def refCellA : Cell :=
  Cell.empty

private def refCellB : Cell :=
  mkCellWithBitsAndRefs (patternBits 5 1) #[]

private def refCellC : Cell :=
  mkCellWithBitsAndRefs (patternBits 7 2) #[refCellA]

private def refCellD : Cell :=
  mkCellWithBitsAndRefs (patternBits 3 3) #[refCellB, refCellA]

private def refCellPool : Array Cell :=
  #[refCellA, refCellB, refCellC, refCellD]

private def mkRefArray (count : Nat) : Array Cell := Id.run do
  let mut refs : Array Cell := #[]
  for i in [0:count] do
    refs := refs.push (refCellPool[i % refCellPool.size]!)
  return refs

private def mkSliceOfSizes (bitCount refCount : Nat) (phase : Nat := 0) : Slice :=
  mkSliceWithBitsAndRefs (patternBits bitCount phase) (mkRefArray refCount)

private def sliceEmpty : Slice :=
  mkSliceOfSizes 0 0

private def sliceBits1Refs0 : Slice :=
  mkSliceOfSizes 1 0

private def sliceBits0Refs1 : Slice :=
  mkSliceOfSizes 0 1

private def sliceBits8Refs2 : Slice :=
  mkSliceOfSizes 8 2 1

private def sliceBits31Refs2 : Slice :=
  mkSliceOfSizes 31 2 2

private def sliceBits63Refs0 : Slice :=
  mkSliceOfSizes 63 0 1

private def sliceBits127Refs3 : Slice :=
  mkSliceOfSizes 127 3 3

private def sliceBits256Refs4 : Slice :=
  mkSliceOfSizes 256 4 2

private def sliceBits511Refs1 : Slice :=
  mkSliceOfSizes 511 1 1

private def sliceBits1023Refs4 : Slice :=
  mkSliceOfSizes 1023 4 4

private def sliceBits0Refs4 : Slice :=
  mkSliceOfSizes 0 4 1

private def sliceBits5Refs4 : Slice :=
  mkSliceOfSizes 5 4 2

private def sliceBits17Refs2 : Slice :=
  mkSliceOfSizes 17 2 4

private def sliceBits19Refs1 : Slice :=
  mkSliceOfSizes 19 1 3

private def sliceShiftBase : Slice :=
  mkSliceOfSizes 40 4 2

private def sliceShiftedBit : Slice :=
  sliceShiftBase.advanceBits 11

private def sliceShiftedRef : Slice :=
  { sliceShiftBase with refPos := 2 }

private def sliceShiftedBoth : Slice :=
  { (mkSliceOfSizes 64 4 3).advanceBits 17 with refPos := 1 }

private def sliceFullyConsumed : Slice :=
  { sliceShiftBase with
      bitPos := sliceShiftBase.cell.bits.size
      refPos := sliceShiftBase.cell.refs.size }

private def slicePastEnd : Slice :=
  { sliceShiftBase with
      bitPos := sliceShiftBase.cell.bits.size + 9
      refPos := sliceShiftBase.cell.refs.size + 2 }

private def fullSliceNoiseA : Slice :=
  mkSliceWithBitsAndRefs (patternBits 13 5) #[refCellD]

private def fullSliceNoiseB : Slice :=
  mkSliceWithBitsAndRefs (patternBits 21 6) #[refCellA, refCellC]

private def expectedSbitrefsOut (below : Array Value) (s : Slice) : Array Value :=
  below ++ #[intV (Int.ofNat s.bitsRemaining), intV (Int.ofNat s.refsRemaining)]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 768, 1023]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (bitsBoundaryPool[idx]!, rng2)
  else
    randNat rng1 0 1023

private def pickRefsMixed (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 4

private def randBitString (bitCount : Nat) (rng0 : StdGen) : BitString × StdGen := Id.run do
  let mut bits : BitString := #[]
  let mut rng := rng0
  for _ in [0:bitCount] do
    let (bit, rng') := randBool rng
    bits := bits.push bit
    rng := rng'
  return (bits, rng)

private def genRefArray (count : Nat) (rng0 : StdGen) : Array Cell × StdGen := Id.run do
  let mut refs : Array Cell := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (idx, rng') := randNat rng 0 (refCellPool.size - 1)
    refs := refs.push (refCellPool[idx]!)
    rng := rng'
  return (refs, rng)

private def mkRandomSlice (bitCount refCount : Nat) (rng0 : StdGen) : Slice × StdGen :=
  let (bits, rng1) := randBitString bitCount rng0
  let (refs, rng2) := genRefArray refCount rng1
  (mkSliceWithBitsAndRefs bits refs, rng2)

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
    (.builder Builder.empty, rng1)
  else if pick = 4 then
    (.tuple #[], rng1)
  else if pick = 5 then
    (.slice fullSliceNoiseA, rng1)
  else
    (.slice fullSliceNoiseB, rng1)

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
    (.builder Builder.empty, "builder", rng1)
  else
    (.tuple #[], "tuple", rng1)

private def genSbitrefsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      (mkSbitrefsCase "fuzz/ok/direct-empty" #[.slice sliceEmpty], rng1)
    else if shape = 1 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      (mkSbitrefsCase s!"fuzz/ok/boundary/bits-{bits}/refs-{refs}" #[.slice s], rng4)
    else if shape = 2 then
      let (bits, rng2) := randNat rng1 0 64
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      (mkSbitrefsCase s!"fuzz/ok/small/bits-{bits}/refs-{refs}" #[.slice s], rng4)
    else if shape = 3 then
      let (bits, rng2) := randNat rng1 257 1023
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      (mkSbitrefsCase s!"fuzz/ok/high/bits-{bits}/refs-{refs}" #[.slice s], rng4)
    else if shape = 4 then
      let (refs, rng2) := randNat rng1 1 4
      let (s, rng3) := mkRandomSlice 0 refs rng2
      (mkSbitrefsCase s!"fuzz/ok/refs-only/refs-{refs}" #[.slice s], rng3)
    else if shape = 5 then
      let (bits, rng2) := pickBitsMixed rng1
      let (s, rng3) := mkRandomSlice bits 0 rng2
      (mkSbitrefsCase s!"fuzz/ok/bits-only/bits-{bits}" #[.slice s], rng3)
    else if shape = 6 then
      let (noise, rng2) := pickNoiseValue rng1
      let (bits, rng3) := pickBitsMixed rng2
      let (refs, rng4) := pickRefsMixed rng3
      let (s, rng5) := mkRandomSlice bits refs rng4
      (mkSbitrefsCase s!"fuzz/ok/deep1/bits-{bits}/refs-{refs}" #[noise, .slice s], rng5)
    else if shape = 7 then
      let (noise1, rng2) := pickNoiseValue rng1
      let (noise2, rng3) := pickNoiseValue rng2
      let (bits, rng4) := pickBitsMixed rng3
      let (refs, rng5) := pickRefsMixed rng4
      let (s, rng6) := mkRandomSlice bits refs rng5
      (mkSbitrefsCase s!"fuzz/ok/deep2/bits-{bits}/refs-{refs}" #[noise1, noise2, .slice s], rng6)
    else if shape = 8 then
      let (refs, rng2) := pickRefsMixed rng1
      let (s, rng3) := mkRandomSlice 1023 refs rng2
      (mkSbitrefsCase s!"fuzz/ok/max-bits/bits-1023/refs-{refs}" #[.slice s], rng3)
    else if shape = 9 then
      (mkSbitrefsCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 10 then
      (mkSbitrefsCase "fuzz/type/top-null" #[.null], rng1)
    else if shape = 11 then
      let (n, rng2) := randNat rng1 0 255
      (mkSbitrefsCase s!"fuzz/type/top-int-{n}" #[intV (Int.ofNat n - 128)], rng2)
    else if shape = 12 then
      (mkSbitrefsCase "fuzz/type/top-cell" #[.cell refCellC], rng1)
    else if shape = 13 then
      (mkSbitrefsCase "fuzz/type/top-builder" #[.builder Builder.empty], rng1)
    else if shape = 14 then
      (mkSbitrefsCase "fuzz/type/top-tuple" #[.tuple #[]], rng1)
    else if shape = 15 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      let (bad, badTag, rng5) := pickBadTopValue rng4
      (mkSbitrefsCase s!"fuzz/type/deep-top-not-slice-{badTag}" #[.slice s, bad], rng5)
    else if shape = 16 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      (mkSbitrefsProgramCase "fuzz/gas/exact"
        #[.slice s]
        #[.pushInt (.num sbitrefsSetGasExact), .tonEnvOp .setGasLimit, sbitrefsInstr], rng4)
    else if shape = 17 then
      let (bits, rng2) := pickBitsMixed rng1
      let (refs, rng3) := pickRefsMixed rng2
      let (s, rng4) := mkRandomSlice bits refs rng3
      (mkSbitrefsProgramCase "fuzz/gas/exact-minus-one"
        #[.slice s]
        #[.pushInt (.num sbitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, sbitrefsInstr], rng4)
    else if shape = 18 then
      let (s, rng2) := mkRandomSlice 1023 4 rng1
      (mkSbitrefsCase "fuzz/ok/stress-max-bits-refs" #[.slice s], rng2)
    else if shape = 19 then
      let (s, rng2) := mkRandomSlice 0 4 rng1
      (mkSbitrefsCase "fuzz/ok/zero-bits-refs4" #[.slice s], rng2)
    else
      let (s, rng2) := mkRandomSlice 256 2 rng1
      (mkSbitrefsCase "fuzz/ok/fixed-bits256-refs2" #[.slice s], rng2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSbitrefsCase "ok/direct-empty" #[.slice sliceEmpty],
    mkSbitrefsCase "ok/bits1-refs0" #[.slice sliceBits1Refs0],
    mkSbitrefsCase "ok/bits0-refs1" #[.slice sliceBits0Refs1],
    mkSbitrefsCase "ok/bits8-refs2" #[.slice sliceBits8Refs2],
    mkSbitrefsCase "ok/bits31-refs2" #[.slice sliceBits31Refs2],
    mkSbitrefsCase "ok/bits63-refs0" #[.slice sliceBits63Refs0],
    mkSbitrefsCase "ok/bits127-refs3" #[.slice sliceBits127Refs3],
    mkSbitrefsCase "ok/bits256-refs4" #[.slice sliceBits256Refs4],
    mkSbitrefsCase "ok/bits511-refs1" #[.slice sliceBits511Refs1],
    mkSbitrefsCase "ok/bits1023-refs4" #[.slice sliceBits1023Refs4],
    mkSbitrefsCase "ok/bits0-refs4" #[.slice sliceBits0Refs4],
    mkSbitrefsCase "ok/bits5-refs4" #[.slice sliceBits5Refs4],
    mkSbitrefsCase "ok/bits17-refs2" #[.slice sliceBits17Refs2],
    mkSbitrefsCase "ok/bits19-refs1" #[.slice sliceBits19Refs1],
    mkSbitrefsCase "ok/deep-preserve-slice-tuple"
      #[.slice fullSliceNoiseA, .tuple #[], .slice sliceBits8Refs2]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkSbitrefsCase "underflow/empty" #[],
    mkSbitrefsCase "type/top-null" #[.null],
    mkSbitrefsCase "type/top-int" #[intV 42],
    mkSbitrefsCase "type/top-cell" #[.cell refCellB],
    mkSbitrefsCase "type/top-builder-empty" #[.builder Builder.empty],
    mkSbitrefsCase "type/top-tuple-empty" #[.tuple #[]],
    mkSbitrefsCase "type/deep-top-not-slice"
      #[.slice sliceBits31Refs2, .null]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkSbitrefsProgramCase "gas/exact-cost-succeeds"
      #[.slice sliceBits63Refs0]
      #[.pushInt (.num sbitrefsSetGasExact), .tonEnvOp .setGasLimit, sbitrefsInstr],
    mkSbitrefsProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice sliceBits63Refs0]
      #[.pushInt (.num sbitrefsSetGasExactMinusOne), .tonEnvOp .setGasLimit, sbitrefsInstr]
  ]

def suite : InstrSuite where
  id := { name := "SBITREFS" }
  unit := #[
    { name := "unit/direct/success-order-and-boundaries"
      run := do
        expectOkStack "ok/empty"
          (runSbitrefsDirect #[.slice sliceEmpty])
          (expectedSbitrefsOut #[] sliceEmpty)

        expectOkStack "ok/bits1-refs0"
          (runSbitrefsDirect #[.slice sliceBits1Refs0])
          (expectedSbitrefsOut #[] sliceBits1Refs0)

        expectOkStack "ok/bits0-refs1"
          (runSbitrefsDirect #[.slice sliceBits0Refs1])
          (expectedSbitrefsOut #[] sliceBits0Refs1)

        expectOkStack "ok/bits31-refs2"
          (runSbitrefsDirect #[.slice sliceBits31Refs2])
          (expectedSbitrefsOut #[] sliceBits31Refs2)

        expectOkStack "ok/bits127-refs3"
          (runSbitrefsDirect #[.slice sliceBits127Refs3])
          (expectedSbitrefsOut #[] sliceBits127Refs3)

        expectOkStack "ok/bits1023-refs4"
          (runSbitrefsDirect #[.slice sliceBits1023Refs4])
          (expectedSbitrefsOut #[] sliceBits1023Refs4)

        expectOkStack "ok/deep-stack-preserved"
          (runSbitrefsDirect #[.null, intV 91, .slice sliceBits31Refs2])
          (expectedSbitrefsOut #[.null, intV 91] sliceBits31Refs2)

        expectOkStack "ok/two-slices-only-top-consumed"
          (runSbitrefsDirect #[.slice sliceBits1Refs0, .slice sliceBits0Refs1])
          #[.slice sliceBits1Refs0, intV 0, intV 1] }
    ,
    { name := "unit/direct/edge-shifted-and-saturated-positions"
      run := do
        expectOkStack "ok/shifted-bit"
          (runSbitrefsDirect #[.slice sliceShiftedBit])
          (expectedSbitrefsOut #[] sliceShiftedBit)

        expectOkStack "ok/shifted-ref"
          (runSbitrefsDirect #[.slice sliceShiftedRef])
          (expectedSbitrefsOut #[] sliceShiftedRef)

        expectOkStack "ok/shifted-both"
          (runSbitrefsDirect #[.slice sliceShiftedBoth])
          (expectedSbitrefsOut #[] sliceShiftedBoth)

        expectOkStack "ok/fully-consumed"
          (runSbitrefsDirect #[.slice sliceFullyConsumed])
          (expectedSbitrefsOut #[] sliceFullyConsumed)

        expectOkStack "ok/past-end-saturates-to-zero"
          (runSbitrefsDirect #[.slice slicePastEnd])
          (expectedSbitrefsOut #[] slicePastEnd)

        expectOkStack "ok/deep-past-end-preserves-below"
          (runSbitrefsDirect #[.slice fullSliceNoiseA, intV (-9), .slice slicePastEnd])
          (expectedSbitrefsOut #[.slice fullSliceNoiseA, intV (-9)] slicePastEnd) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty"
          (runSbitrefsDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runSbitrefsDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runSbitrefsDirect #[intV 7]) .typeChk
        expectErr "type/top-cell"
          (runSbitrefsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-builder"
          (runSbitrefsDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple"
          (runSbitrefsDirect #[.tuple #[]]) .typeChk

        expectErr "type/deep-top-not-slice-null"
          (runSbitrefsDirect #[.slice sliceBits31Refs2, .null]) .typeChk
        expectErr "type/deep-top-not-slice-cell"
          (runSbitrefsDirect #[.slice sliceBits31Refs2, .cell refCellC]) .typeChk }
    ,
    { name := "unit/direct/rangechk-unreachable-for-sbitrefs"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("success", runSbitrefsDirect #[.slice sliceBits31Refs2]),
            ("success-shifted", runSbitrefsDirect #[.slice sliceShiftedBoth]),
            ("underflow", runSbitrefsDirect #[]),
            ("type", runSbitrefsDirect #[.builder Builder.empty])
          ]
        for p in probes do
          match p.2 with
          | .error .rangeChk =>
              throw (IO.userError s!"{p.1}: unexpected rangeChk for SBITREFS")
          | _ => pure () }
    ,
    { name := "unit/opcode/decode-assembler-boundary-and-gap"
      run := do
        let single ←
          match assembleCp0 [sbitrefsInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sbitrefs failed: {e}")
        if single.bits = natToBits sbitrefsWord 16 then
          pure ()
        else
          throw (IO.userError s!"sbitrefs canonical encode mismatch: got bits {single.bits}")
        if single.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"sbitrefs encode width mismatch: got {single.bits.size} bits")

        let program : Array Instr :=
          #[.cellOp .pldRefVar, .sbits, .srefs, sbitrefsInstr, .pldRefIdx 2, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pldrefvar-neighbor" s0 (.cellOp .pldRefVar) 16
        let s2 ← expectDecodeStep "decode/sbits-neighbor" s1 .sbits 16
        let s3 ← expectDecodeStep "decode/srefs-neighbor" s2 .srefs 16
        let s4 ← expectDecodeStep "decode/sbitrefs" s3 sbitrefsInstr 16
        let s5 ← expectDecodeStep "decode/pldrefidx2-neighbor" s4 (.pldRefIdx 2) 16
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let addCode ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble add failed: {e}")
        let rawBits : BitString :=
          natToBits 0xd748 16 ++
            natToBits 0xd749 16 ++
            natToBits 0xd74a 16 ++
            natToBits sbitrefsWord 16 ++
            natToBits 0xd74c 16 ++
            natToBits 0xd74f 16 ++
            addCode.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-0xd748-pldrefvar" r0 (.cellOp .pldRefVar) 16
        let r2 ← expectDecodeStep "decode/raw-0xd749-sbits" r1 .sbits 16
        let r3 ← expectDecodeStep "decode/raw-0xd74a-srefs" r2 .srefs 16
        let r4 ← expectDecodeStep "decode/raw-0xd74b-sbitrefs" r3 sbitrefsInstr 16
        let r5 ← expectDecodeStep "decode/raw-0xd74c-pldrefidx0" r4 (.pldRefIdx 0) 16
        let r6 ← expectDecodeStep "decode/raw-0xd74f-pldrefidx3" r5 (.pldRefIdx 3) 16
        let r7 ← expectDecodeStep "decode/raw-tail-add" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining")

        expectDecodeErr "decode/raw-gap-d744"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xd744 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-handled"
      run := do
        expectOkStack "dispatch/non-sbitrefs-add"
          (runSbitrefsDispatchWithNext .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-sbitrefs-sbits"
          (runSbitrefsDispatchWithNext .sbits #[.slice sliceBits1Refs0])
          #[.slice sliceBits1Refs0, intV dispatchSentinel]
        expectOkStack "dispatch/non-sbitrefs-srefs"
          (runSbitrefsDispatchWithNext .srefs #[.tuple #[]])
          #[.tuple #[], intV dispatchSentinel]
        expectOkStack "dispatch/non-sbitrefs-pldrefvar"
          (runSbitrefsDispatchWithNext (.cellOp .pldRefVar) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]

        expectOkStack "dispatch/handled-sbitrefs-does-not-run-next"
          (runSbitrefsDispatchWithNext sbitrefsInstr #[.slice sliceBits31Refs2])
          #[intV 31, intV 2]
        expectOkStack "dispatch/handled-sbitrefs-deep"
          (runSbitrefsDispatchWithNext sbitrefsInstr #[.null, .slice sliceShiftedBoth])
          (expectedSbitrefsOut #[.null] sliceShiftedBoth) }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021091
      count := 320
      gen := genSbitrefsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SBITREFS
