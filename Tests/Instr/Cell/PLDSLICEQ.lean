import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.PLDSLICEQ

/-
PLDSLICEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceFixed.lean` (`.loadSliceFixed prefetch quiet bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.loadSliceFixed true true bits` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd71c>>2` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice_fixed2` → `exec_load_slice_common`).

Quiet fixed-width contract (prefetch + quiet `PLDSLICEQ`) verified against C++:
- success (`have(bits)`): push loaded prefix slice, then `-1`; no remainder push in prefetch mode;
- failure (`!have(bits)`): no exception, push only `0` (original slice is not re-pushed when prefetch=true);
- underflow/type failures happen at initial slice pop, before quiet status behavior.

Key risk areas covered:
- quiet status polarity (`-1` success vs `0` failure);
- prefetch-specific stack shape (no remainder on success, no slice re-push on quiet failure);
- deep-stack preservation beneath consumed top slice;
- decode/assembler distinction for `{P}LDSLICE{Q}` fixed-width opcodes.
-/

private def pldsliceqId : InstrId := { name := "PLDSLICEQ" }

private def pldsliceqInstr (bits : Nat) : Instr :=
  .loadSliceFixed true true bits

private def pldsliceqGasInstr : Instr :=
  pldsliceqInstr 8

private def mkPldsliceqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[pldsliceqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPldsliceqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := pldsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runPldsliceqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceFixed (pldsliceqInstr bits) stack

private def runPldsliceqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceFixed instr (VM.push (intV 742)) stack

private def pldsliceqSetGasExact : Int :=
  computeExactGasBudget pldsliceqGasInstr

private def pldsliceqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne pldsliceqGasInstr

private def alternatingBits (n : Nat) : BitString :=
  Array.ofFn (n := n) fun i => i.1 % 2 = 0

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3)

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 13 4)

private def mkSliceWithRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary bits refs)

private def mkPatternSlice (n : Nat) : Slice :=
  mkSliceFromBits (alternatingBits n)

private def mkPatternSliceWithRefs (n : Nat) (refs : Array Cell := #[refLeafA]) : Slice :=
  mkSliceWithRefs (alternatingBits n) refs

private def loadedPrefixSlice (s : Slice) (bits : Nat) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (s.readBits bits) #[])

private def pldsliceqWord24 (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags2 : Nat := 0x3
  let args10 : Nat := (flags2 <<< 8) + bits8
  let prefix14 : Nat := 0xd71c >>> 2
  (prefix14 <<< 10) + args10

private def pldsliceqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickPldsliceqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pldsliceqWidthBoundaryPool.size - 1)
  (pldsliceqWidthBoundaryPool[idx]!, rng')

private def pickPldsliceqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickPldsliceqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickPldsliceqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickPldsliceqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickPldsliceqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickPldsliceqNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else .cell Cell.empty
  (v, rng1)

private def genPldsliceqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (bits, rng2) := pickPldsliceqWidthMixed rng1
  if shape = 0 then
    (mkPldsliceqCase s!"fuzz/ok/exact/w-{bits}" bits #[.slice (mkPatternSlice bits)], rng2)
  else if shape = 1 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast bits rng2
    (mkPldsliceqCase s!"fuzz/ok/extra/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 2 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast bits rng2
    let (refs, rng4) := pickPldsliceqRefPackNonEmpty rng3
    (mkPldsliceqCase s!"fuzz/ok/refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 3 then
    let (avail, rng3) := pickPldsliceqAvailBelow bits rng2
    (mkPldsliceqCase s!"fuzz/fail/short/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 4 then
    let (avail, rng3) := pickPldsliceqAvailBelow bits rng2
    let (refs, rng4) := pickPldsliceqRefPackNonEmpty rng3
    (mkPldsliceqCase s!"fuzz/fail/short-refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 5 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast bits rng2
    let (noise, rng4) := pickPldsliceqNoiseValue rng3
    (mkPldsliceqCase s!"fuzz/ok/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 6 then
    let (avail, rng3) := pickPldsliceqAvailBelow bits rng2
    let (noise, rng4) := pickPldsliceqNoiseValue rng3
    (mkPldsliceqCase s!"fuzz/fail/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 7 then
    (mkPldsliceqCase "fuzz/underflow/empty" bits #[], rng2)
  else if shape = 8 then
    (mkPldsliceqCase s!"fuzz/type/top-null/w-{bits}" bits #[.null], rng2)
  else if shape = 9 then
    (mkPldsliceqCase s!"fuzz/type/top-int/w-{bits}" bits #[intV 5], rng2)
  else if shape = 10 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast bits rng2
    (mkPldsliceqCase s!"fuzz/type/deep-top-not-slice/w-{bits}-a-{avail}" bits
      #[.slice (mkPatternSlice avail), .null], rng3)
  else if shape = 11 then
    (mkPldsliceqCase s!"fuzz/fail/zero-available/w-{bits}" bits #[.slice (mkPatternSlice 0)], rng2)
  else if shape = 12 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast 8 rng2
    (mkPldsliceqProgramCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice avail)]
      #[.pushInt (.num pldsliceqSetGasExact), .tonEnvOp .setGasLimit, pldsliceqGasInstr], rng3)
  else if shape = 13 then
    let (avail, rng3) := pickPldsliceqAvailAtLeast 8 rng2
    (mkPldsliceqProgramCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice avail)]
      #[.pushInt (.num pldsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldsliceqGasInstr], rng3)
  else if shape = 14 then
    let bits' := if bits = 256 then 255 else bits
    let avail := bits' + 1
    (mkPldsliceqCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkPldsliceqCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)

def suite : InstrSuite where
  id := pldsliceqId
  unit := #[
    { name := "unit/direct/quiet-success-stack-order-status-minus1-and-no-remainder"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (1, 1),
            (1, 5),
            (2, 2),
            (7, 11),
            (8, 8),
            (16, 20),
            (64, 80),
            (127, 140),
            (256, 256)
          ]
        for c in checks do
          let bits := c.1
          let avail := c.2
          let input := mkPatternSlice avail
          let loaded := loadedPrefixSlice input bits
          expectOkStack s!"ok/w-{bits}-a-{avail}"
            (runPldsliceqDirect bits #[.slice input])
            #[.slice loaded, intV (-1)]

        let refsInput := mkPatternSliceWithRefs 12 #[refLeafA, refLeafB]
        let refsLoaded := loadedPrefixSlice refsInput 9
        expectOkStack "ok/refs/w-9-a-12-r-2"
          (runPldsliceqDirect 9 #[.slice refsInput])
          #[.slice refsLoaded, intV (-1)]

        let refsWide := mkPatternSliceWithRefs 256 #[refLeafA]
        let refsWideLoaded := loadedPrefixSlice refsWide 256
        expectOkStack "ok/refs/w-256-a-256-r-1"
          (runPldsliceqDirect 256 #[.slice refsWide])
          #[.slice refsWideLoaded, intV (-1)]

        let deep := mkPatternSlice 14
        let deepLoaded := loadedPrefixSlice deep 9
        expectOkStack "ok/deep-stack-preserve-below"
          (runPldsliceqDirect 9 #[.null, intV 33, .slice deep])
          #[.null, intV 33, .slice deepLoaded, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-status0-only-no-slice-repush"
      run := do
        let checks : Array (Nat × Nat) :=
          #[
            (1, 0),
            (2, 1),
            (8, 7),
            (16, 0),
            (64, 63),
            (128, 127),
            (256, 255)
          ]
        for c in checks do
          let bits := c.1
          let avail := c.2
          let input := mkPatternSlice avail
          expectOkStack s!"fail/w-{bits}-a-{avail}"
            (runPldsliceqDirect bits #[.slice input])
            #[intV 0]

        let refsInput := mkPatternSliceWithRefs 4 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runPldsliceqDirect 5 #[.slice refsInput])
          #[intV 0]

        let deep := mkPatternSlice 10
        expectOkStack "fail/deep-stack-preserve-below"
          (runPldsliceqDirect 64 #[intV 77, .slice deep])
          #[intV 77, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty" (runPldsliceqDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runPldsliceqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runPldsliceqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runPldsliceqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runPldsliceqDirect 8 #[.slice (mkPatternSlice 9), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-range-and-raw"
      run := do
        let program : Array Instr :=
          #[
            pldsliceqInstr 1,
            pldsliceqInstr 17,
            pldsliceqInstr 256,
            .loadSliceFixed false true 5,
            .loadSliceFixed true false 5,
            .loadSliceFixed false false 5,
            .add
          ]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/pldsliceq-1" s0 (pldsliceqInstr 1) 24
        let s2 ← expectDecodeStep "decode/pldsliceq-17" s1 (pldsliceqInstr 17) 24
        let s3 ← expectDecodeStep "decode/pldsliceq-256" s2 (pldsliceqInstr 256) 24
        let s4 ← expectDecodeStep "decode/ldsliceq-5" s3 (.loadSliceFixed false true 5) 24
        let s5 ← expectDecodeStep "decode/pldslice-5" s4 (.loadSliceFixed true false 5) 24
        let s6 ← expectDecodeStep "decode/ldslice-5" s5 (.loadSliceFixed false false 5) 24
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits (pldsliceqWord24 42) 24 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-pldsliceq-42" raw (pldsliceqInstr 42) 24
        let raw2 ← expectDecodeStep "decode/raw-tail-add" raw1 .add 8
        if raw2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {raw2.bitsRemaining} bits remaining")

        let checkRangeChk := fun (label : String) (res : Except Excno Cell) => do
          match res with
          | .error .rangeChk => pure ()
          | .error e => throw (IO.userError s!"{label}: expected rangeChk, got {e}")
          | .ok _ => throw (IO.userError s!"{label}: expected rangeChk, got successful assembly")
        checkRangeChk "asm/range/bits-0" (assembleCp0 [pldsliceqInstr 0])
        checkRangeChk "asm/range/bits-257" (assembleCp0 [pldsliceqInstr 257]) }
    ,
    { name := "unit/dispatch/non-loadslicefixed-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runPldsliceqDispatchFallback .add #[.null])
          #[.null, intV 742]
        expectOkStack "dispatch/loadslicex-not-handled-here"
          (runPldsliceqDispatchFallback (.loadSliceX true true) #[intV (-3)])
          #[intV (-3), intV 742] }
  ]
  oracle := #[
    mkPldsliceqCase "ok/w-1-a-1" 1 #[.slice (mkPatternSlice 1)],
    mkPldsliceqCase "ok/w-1-a-5" 1 #[.slice (mkPatternSlice 5)],
    mkPldsliceqCase "ok/w-2-a-2" 2 #[.slice (mkPatternSlice 2)],
    mkPldsliceqCase "ok/w-7-a-11" 7 #[.slice (mkPatternSlice 11)],
    mkPldsliceqCase "ok/w-8-a-8" 8 #[.slice (mkPatternSlice 8)],
    mkPldsliceqCase "ok/w-16-a-20" 16 #[.slice (mkPatternSlice 20)],
    mkPldsliceqCase "ok/w-31-a-63" 31 #[.slice (mkPatternSlice 63)],
    mkPldsliceqCase "ok/w-64-a-64" 64 #[.slice (mkPatternSlice 64)],
    mkPldsliceqCase "ok/w-127-a-140" 127 #[.slice (mkPatternSlice 140)],
    mkPldsliceqCase "ok/w-128-a-256" 128 #[.slice (mkPatternSlice 256)],
    mkPldsliceqCase "ok/w-255-a-255" 255 #[.slice (mkPatternSlice 255)],
    mkPldsliceqCase "ok/w-256-a-256" 256 #[.slice (mkPatternSlice 256)],
    mkPldsliceqCase "ok/deep-stack-null-below" 9 #[.null, .slice (mkPatternSlice 14)],
    mkPldsliceqCase "ok/deep-stack-two-below" 5 #[intV (-7), .null, .slice (mkPatternSlice 9)],
    mkPldsliceqCase "ok/refs/w-9-a-12-r-2" 9 #[.slice (mkPatternSliceWithRefs 12 #[refLeafA, refLeafB])],
    mkPldsliceqCase "ok/refs/w-256-a-256-r-1" 256 #[.slice (mkPatternSliceWithRefs 256 #[refLeafA])],

    mkPldsliceqCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0)],
    mkPldsliceqCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1)],
    mkPldsliceqCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7)],
    mkPldsliceqCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0)],
    mkPldsliceqCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63)],
    mkPldsliceqCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127)],
    mkPldsliceqCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255)],
    mkPldsliceqCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10)],
    mkPldsliceqCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 #[refLeafA])],
    mkPldsliceqCase "fail/refs/w-256-a-128-r-2" 256 #[.slice (mkPatternSliceWithRefs 128 #[refLeafA, refLeafB])],

    mkPldsliceqCase "underflow/empty" 8 #[],
    mkPldsliceqCase "type/top-null" 8 #[.null],
    mkPldsliceqCase "type/top-int" 8 #[intV 5],
    mkPldsliceqCase "type/deep-top-not-slice" 8 #[.slice (mkPatternSlice 8), .null],

    mkPldsliceqProgramCase "gas/exact-cost-succeeds"
      #[.slice (mkPatternSlice 14)]
      #[.pushInt (.num pldsliceqSetGasExact), .tonEnvOp .setGasLimit, pldsliceqGasInstr],
    mkPldsliceqProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPatternSlice 14)]
      #[.pushInt (.num pldsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, pldsliceqGasInstr]
  ]
  fuzz := #[
    { seed := 2026021025
      count := 320
      gen := genPldsliceqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.PLDSLICEQ
