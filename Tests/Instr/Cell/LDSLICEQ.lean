import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSLICEQ

/-
LDSLICEQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/LoadSliceFixed.lean` (`.loadSliceFixed prefetch quiet bits`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.loadSliceFixed false true bits` encode path)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd71c>>2` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_load_slice_fixed2` → `exec_load_slice_common`).

Quiet fixed-width contract (non-prefetch `LDSLICEQ`) verified against C++:
- success (`have(bits)`): push loaded prefix slice, then remainder slice, then `-1`;
- failure (`!have(bits)`): no exception, push original slice, then `0`;
- underflow/type failures happen at the initial slice pop, before quiet status behavior.

Key risk areas covered:
- quiet status polarity (`-1` success vs `0` failure);
- stack order on success/failure in non-prefetch mode;
- original-slice preservation on quiet failure;
- decode/assembler distinction for `{P}LDSLICE{Q}` fixed-width opcodes.
-/

private def ldsliceqId : InstrId := { name := "LDSLICEQ" }

private def ldsliceqInstr (bits : Nat) : Instr :=
  .loadSliceFixed false true bits

private def ldsliceqGasInstr : Instr :=
  ldsliceqInstr 8

private def mkLdsliceqCase
    (name : String)
    (bits : Nat)
    (stack : Array Value)
    (program : Array Instr := #[ldsliceqInstr bits])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkLdsliceqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldsliceqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdsliceqDirect (bits : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellLoadSliceFixed (ldsliceqInstr bits) stack

private def runLdsliceqDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellLoadSliceFixed instr (VM.push (intV 742)) stack

private def ldsliceqSetGasExact : Int :=
  computeExactGasBudget ldsliceqGasInstr

private def ldsliceqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldsliceqGasInstr

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

private def ldsliceqWord24 (bits : Nat) : Nat :=
  let bits8 : Nat := bits - 1
  let flags2 : Nat := 0x2
  let args10 : Nat := (flags2 <<< 8) + bits8
  let prefix14 : Nat := 0xd71c >>> 2
  (prefix14 <<< 10) + args10

private def ldsliceqWidthBoundaryPool : Array Nat :=
  #[1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickLdsliceqWidthBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (ldsliceqWidthBoundaryPool.size - 1)
  (ldsliceqWidthBoundaryPool[idx]!, rng')

private def pickLdsliceqWidthMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickLdsliceqWidthBoundary rng1
  else
    randNat rng1 1 256

private def pickLdsliceqAvailAtLeast (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  let maxExtra : Nat := Nat.min 64 (1023 - bits)
  let (extra, rng1) := randNat rng0 0 maxExtra
  (bits + extra, rng1)

private def pickLdsliceqAvailBelow (bits : Nat) (rng0 : StdGen) : Nat × StdGen :=
  if bits = 0 then
    (0, rng0)
  else
    randNat rng0 0 (bits - 1)

private def pickLdsliceqRefPackNonEmpty (rng0 : StdGen) : Array Cell × StdGen :=
  let (pick, rng1) := randNat rng0 0 1
  if pick = 0 then
    (#[refLeafA], rng1)
  else
    (#[refLeafA, refLeafB], rng1)

private def pickLdsliceqNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 19
    else .cell Cell.empty
  (v, rng1)

private def genLdsliceqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (bits, rng2) := pickLdsliceqWidthMixed rng1
  if shape = 0 then
    (mkLdsliceqCase s!"fuzz/ok/exact/w-{bits}" bits #[.slice (mkPatternSlice bits)], rng2)
  else if shape = 1 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast bits rng2
    (mkLdsliceqCase s!"fuzz/ok/extra/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 2 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast bits rng2
    let (refs, rng4) := pickLdsliceqRefPackNonEmpty rng3
    (mkLdsliceqCase s!"fuzz/ok/refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 3 then
    let (avail, rng3) := pickLdsliceqAvailBelow bits rng2
    (mkLdsliceqCase s!"fuzz/fail/short/w-{bits}-a-{avail}" bits #[.slice (mkPatternSlice avail)], rng3)
  else if shape = 4 then
    let (avail, rng3) := pickLdsliceqAvailBelow bits rng2
    let (refs, rng4) := pickLdsliceqRefPackNonEmpty rng3
    (mkLdsliceqCase s!"fuzz/fail/short-refs/w-{bits}-a-{avail}-r-{refs.size}" bits
      #[.slice (mkPatternSliceWithRefs avail refs)], rng4)
  else if shape = 5 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast bits rng2
    let (noise, rng4) := pickLdsliceqNoiseValue rng3
    (mkLdsliceqCase s!"fuzz/ok/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 6 then
    let (avail, rng3) := pickLdsliceqAvailBelow bits rng2
    let (noise, rng4) := pickLdsliceqNoiseValue rng3
    (mkLdsliceqCase s!"fuzz/fail/deep-stack/w-{bits}-a-{avail}" bits
      #[noise, .slice (mkPatternSlice avail)], rng4)
  else if shape = 7 then
    (mkLdsliceqCase "fuzz/underflow/empty" bits #[], rng2)
  else if shape = 8 then
    (mkLdsliceqCase s!"fuzz/type/top-null/w-{bits}" bits #[.null], rng2)
  else if shape = 9 then
    (mkLdsliceqCase s!"fuzz/type/top-int/w-{bits}" bits #[intV 5], rng2)
  else if shape = 10 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast bits rng2
    (mkLdsliceqCase s!"fuzz/type/deep-top-not-slice/w-{bits}-a-{avail}" bits
      #[.slice (mkPatternSlice avail), .null], rng3)
  else if shape = 11 then
    (mkLdsliceqCase s!"fuzz/fail/zero-available/w-{bits}" bits #[.slice (mkPatternSlice 0)], rng2)
  else if shape = 12 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast 8 rng2
    (mkLdsliceqProgramCase "fuzz/gas/exact"
      #[.slice (mkPatternSlice avail)]
      #[.pushInt (.num ldsliceqSetGasExact), .tonEnvOp .setGasLimit, ldsliceqGasInstr], rng3)
  else if shape = 13 then
    let (avail, rng3) := pickLdsliceqAvailAtLeast 8 rng2
    (mkLdsliceqProgramCase "fuzz/gas/exact-minus-one"
      #[.slice (mkPatternSlice avail)]
      #[.pushInt (.num ldsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldsliceqGasInstr], rng3)
  else if shape = 14 then
    let bits' := if bits = 256 then 255 else bits
    let avail := bits' + 1
    (mkLdsliceqCase s!"fuzz/ok/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)
  else
    let bits' := if bits = 1 then 2 else bits
    let avail := bits' - 1
    (mkLdsliceqCase s!"fuzz/fail/near-boundary/w-{bits'}-a-{avail}" bits'
      #[.slice (mkPatternSlice avail)], rng2)

def suite : InstrSuite where
  id := ldsliceqId
  unit := #[
    { name := "unit/direct/quiet-success-stack-order-and-status-minus1"
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
          let rem := input.advanceBits bits
          expectOkStack s!"ok/w-{bits}-a-{avail}"
            (runLdsliceqDirect bits #[.slice input])
            #[.slice loaded, .slice rem, intV (-1)]

        let refsInput := mkPatternSliceWithRefs 12 #[refLeafA, refLeafB]
        let refsLoaded := loadedPrefixSlice refsInput 9
        let refsRem := refsInput.advanceBits 9
        expectOkStack "ok/refs/w-9-a-12-r-2"
          (runLdsliceqDirect 9 #[.slice refsInput])
          #[.slice refsLoaded, .slice refsRem, intV (-1)]

        let refsWide := mkPatternSliceWithRefs 256 #[refLeafA]
        let refsWideLoaded := loadedPrefixSlice refsWide 256
        let refsWideRem := refsWide.advanceBits 256
        expectOkStack "ok/refs/w-256-a-256-r-1"
          (runLdsliceqDirect 256 #[.slice refsWide])
          #[.slice refsWideLoaded, .slice refsWideRem, intV (-1)]

        let deep := mkPatternSlice 14
        let deepLoaded := loadedPrefixSlice deep 9
        let deepRem := deep.advanceBits 9
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdsliceqDirect 9 #[.null, intV 33, .slice deep])
          #[.null, intV 33, .slice deepLoaded, .slice deepRem, intV (-1)] }
    ,
    { name := "unit/direct/quiet-failure-preserves-original-slice-and-status0"
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
            (runLdsliceqDirect bits #[.slice input])
            #[.slice input, intV 0]

        let refsInput := mkPatternSliceWithRefs 4 #[refLeafA, refLeafB]
        expectOkStack "fail/refs/w-5-a-4-r-2"
          (runLdsliceqDirect 5 #[.slice refsInput])
          #[.slice refsInput, intV 0]

        let deep := mkPatternSlice 10
        expectOkStack "fail/deep-stack-preserve-below"
          (runLdsliceqDirect 64 #[intV 77, .slice deep])
          #[intV 77, .slice deep, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type-ordering"
      run := do
        expectErr "underflow/empty" (runLdsliceqDirect 8 #[]) .stkUnd
        expectErr "type/top-null" (runLdsliceqDirect 8 #[.null]) .typeChk
        expectErr "type/top-int" (runLdsliceqDirect 8 #[intV 5]) .typeChk
        expectErr "type/top-cell" (runLdsliceqDirect 8 #[.cell Cell.empty]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdsliceqDirect 8 #[.slice (mkPatternSlice 9), .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-range-and-raw"
      run := do
        let program : Array Instr :=
          #[ldsliceqInstr 1, ldsliceqInstr 17, ldsliceqInstr 256, .loadSliceFixed true true 5, .loadSliceFixed false false 5, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldsliceq-1" s0 (ldsliceqInstr 1) 24
        let s2 ← expectDecodeStep "decode/ldsliceq-17" s1 (ldsliceqInstr 17) 24
        let s3 ← expectDecodeStep "decode/ldsliceq-256" s2 (ldsliceqInstr 256) 24
        let s4 ← expectDecodeStep "decode/pldsliceq-5" s3 (.loadSliceFixed true true 5) 24
        let s5 ← expectDecodeStep "decode/ldslice-alt-5" s4 (.loadSliceFixed false false 5) 24
        let s6 ← expectDecodeStep "decode/tail-add" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let raw := mkSliceFromBits (natToBits (ldsliceqWord24 42) 24 ++ natToBits 0xa0 8)
        let raw1 ← expectDecodeStep "decode/raw-ldsliceq-42" raw (ldsliceqInstr 42) 24
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
        checkRangeChk "asm/range/bits-0" (assembleCp0 [ldsliceqInstr 0])
        checkRangeChk "asm/range/bits-257" (assembleCp0 [ldsliceqInstr 257]) }
    ,
    { name := "unit/dispatch/non-loadslicefixed-falls-through"
      run := do
        expectOkStack "dispatch/non-cell-instr"
          (runLdsliceqDispatchFallback .add #[.null])
          #[.null, intV 742]
        expectOkStack "dispatch/loadslicex-not-handled-here"
          (runLdsliceqDispatchFallback (.loadSliceX false true) #[intV (-3)])
          #[intV (-3), intV 742] }
  ]
  oracle := #[
    mkLdsliceqCase "ok/w-1-a-1" 1 #[.slice (mkPatternSlice 1)],
    mkLdsliceqCase "ok/w-1-a-5" 1 #[.slice (mkPatternSlice 5)],
    mkLdsliceqCase "ok/w-2-a-2" 2 #[.slice (mkPatternSlice 2)],
    mkLdsliceqCase "ok/w-7-a-11" 7 #[.slice (mkPatternSlice 11)],
    mkLdsliceqCase "ok/w-8-a-8" 8 #[.slice (mkPatternSlice 8)],
    mkLdsliceqCase "ok/w-16-a-20" 16 #[.slice (mkPatternSlice 20)],
    mkLdsliceqCase "ok/w-31-a-63" 31 #[.slice (mkPatternSlice 63)],
    mkLdsliceqCase "ok/w-64-a-64" 64 #[.slice (mkPatternSlice 64)],
    mkLdsliceqCase "ok/w-127-a-140" 127 #[.slice (mkPatternSlice 140)],
    mkLdsliceqCase "ok/w-128-a-256" 128 #[.slice (mkPatternSlice 256)],
    mkLdsliceqCase "ok/w-255-a-255" 255 #[.slice (mkPatternSlice 255)],
    mkLdsliceqCase "ok/w-256-a-256" 256 #[.slice (mkPatternSlice 256)],
    mkLdsliceqCase "ok/deep-stack-null-below" 9 #[.null, .slice (mkPatternSlice 14)],
    mkLdsliceqCase "ok/deep-stack-two-below" 5 #[intV (-7), .null, .slice (mkPatternSlice 9)],
    mkLdsliceqCase "ok/refs/w-9-a-12-r-2" 9 #[.slice (mkPatternSliceWithRefs 12 #[refLeafA, refLeafB])],
    mkLdsliceqCase "ok/refs/w-256-a-256-r-1" 256 #[.slice (mkPatternSliceWithRefs 256 #[refLeafA])],

    mkLdsliceqCase "fail/w-1-a-0" 1 #[.slice (mkPatternSlice 0)],
    mkLdsliceqCase "fail/w-2-a-1" 2 #[.slice (mkPatternSlice 1)],
    mkLdsliceqCase "fail/w-8-a-7" 8 #[.slice (mkPatternSlice 7)],
    mkLdsliceqCase "fail/w-16-a-0" 16 #[.slice (mkPatternSlice 0)],
    mkLdsliceqCase "fail/w-64-a-63" 64 #[.slice (mkPatternSlice 63)],
    mkLdsliceqCase "fail/w-128-a-127" 128 #[.slice (mkPatternSlice 127)],
    mkLdsliceqCase "fail/w-256-a-255" 256 #[.slice (mkPatternSlice 255)],
    mkLdsliceqCase "fail/deep-stack/w-64-a-10" 64 #[intV 33, .slice (mkPatternSlice 10)],
    mkLdsliceqCase "fail/refs/w-5-a-4-r-1" 5 #[.slice (mkPatternSliceWithRefs 4 #[refLeafA])],
    mkLdsliceqCase "fail/refs/w-256-a-128-r-2" 256 #[.slice (mkPatternSliceWithRefs 128 #[refLeafA, refLeafB])],

    mkLdsliceqCase "underflow/empty" 8 #[],
    mkLdsliceqCase "type/top-null" 8 #[.null],
    mkLdsliceqCase "type/top-int" 8 #[intV 5],
    mkLdsliceqCase "type/deep-top-not-slice" 8 #[.slice (mkPatternSlice 8), .null],

    mkLdsliceqProgramCase "gas/exact-cost-succeeds"
      #[.slice (mkPatternSlice 14)]
      #[.pushInt (.num ldsliceqSetGasExact), .tonEnvOp .setGasLimit, ldsliceqGasInstr],
    mkLdsliceqProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice (mkPatternSlice 14)]
      #[.pushInt (.num ldsliceqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldsliceqGasInstr]
  ]
  fuzz := #[
    { seed := 2026021024
      count := 320
      gen := genLdsliceqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSLICEQ
