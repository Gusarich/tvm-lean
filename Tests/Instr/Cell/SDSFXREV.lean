import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDSFXREV

/-
SDSFXREV branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdSfxRev`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SDSFXREV` encode `0xc70d`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc70d` decode to `.cellOp .sdSfxRev`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_bin_cs_cmp`; registration `0xc70d` = `cs2->is_suffix_of(*cs1)`).

Branch map used for this suite:
- dispatch guard: only `.cellOp .sdSfxRev` is handled, all other instructions pass to `next`;
- error path 1: `checkUnderflow 2` -> `stkUnd`;
- error path 2: `popSlice` type checks for top and then next stack element -> `typeChk`;
- success path: push `-1` when top slice is a suffix of the next slice by remaining bits;
- false path: push `0` when not a suffix (including "suffix longer than whole");
- bit-only compare contract: refs are ignored, and comparison uses remaining bits of slices;
- decode/assembler boundaries in the `0xc70c..0xc70f` family around exact opcode `0xc70d`.
-/

private def sdsfxrevId : InstrId := { name := "SDSFXREV" }

private def sdsfxrevInstr : Instr := .cellOp .sdSfxRev
private def sdsfxInstr : Instr := .cellOp .sdSfx
private def sdpsfxInstr : Instr := .cellOp .sdPsfx
private def sdpsfxrevInstr : Instr := .cellOp .sdPsfxRev

private def sdsfxrevOpcode : Nat := 0xc70d

private def dispatchSentinel : Int := 7045

private def execInstrCellOpSdsfxrevOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdSfxRev =>
      execCellOpExt .sdSfxRev next
  | _ =>
      next

private def mkSdsfxrevCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdsfxrevInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdsfxrevId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdsfxrevDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdsfxrevOnly sdsfxrevInstr stack

private def runSdsfxrevDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSdsfxrevOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def mkSliceWithBits (bits : BitString) : Slice :=
  mkSliceWithBitsRefs bits #[]

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 5 3) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 11 4) #[]

private def refLeafC : Cell :=
  Cell.mkOrdinary (natToBits 3 2) #[]

private def wholeBitsA : BitString :=
  natToBits 42 6 ++ natToBits 5 3

private def suffixBitsA : BitString :=
  natToBits 5 3

private def prefixBitsA : BitString :=
  natToBits 42 6

private def nonSuffixBitsA : BitString :=
  natToBits 6 3

private def longerBitsA : BitString :=
  wholeBitsA.push true

private def wholeA : Slice := mkSliceWithBits wholeBitsA
private def suffixA : Slice := mkSliceWithBits suffixBitsA
private def prefixA : Slice := mkSliceWithBits prefixBitsA
private def nonSuffixA : Slice := mkSliceWithBits nonSuffixBitsA
private def longerA : Slice := mkSliceWithBits longerBitsA
private def emptySlice : Slice := mkSliceWithBits #[]

private def wholeWithRefs : Slice :=
  mkSliceWithBitsRefs wholeBitsA #[refLeafA, refLeafB]

private def suffixWithOtherRefs : Slice :=
  mkSliceWithBitsRefs suffixBitsA #[refLeafC]

private def sdsfxrevSetGasExact : Int :=
  computeExactGasBudget sdsfxrevInstr

private def sdsfxrevSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdsfxrevInstr

private def mkUnitBoolCase
    (name : String)
    (whole : Slice)
    (suffix : Slice)
    (expected : Int)
    (below : Array Value := #[]) : UnitCase :=
  { name := name
    run := do
      expectOkStack name
        (runSdsfxrevDirect (below ++ #[.slice whole, .slice suffix]))
        (below ++ #[intV expected]) }

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkSdsfxrevCase "ok/empty-suffix-on-nonempty"
      #[.slice wholeA, .slice emptySlice],
    mkSdsfxrevCase "ok/both-empty"
      #[.slice emptySlice, .slice emptySlice],
    mkSdsfxrevCase "ok/equal-length-equal-bits"
      #[.slice wholeA, .slice wholeA],
    mkSdsfxrevCase "ok/strict-suffix"
      #[.slice wholeA, .slice suffixA],
    mkSdsfxrevCase "ok/refs-ignored"
      #[.slice wholeWithRefs, .slice suffixWithOtherRefs],
    mkSdsfxrevCase "ok/deep-stack-preserved"
      #[intV 91, .null, .slice wholeA, .slice suffixA]
  ]

private def oracleFalseCases : Array OracleCase :=
  #[
    mkSdsfxrevCase "false/non-suffix"
      #[.slice wholeA, .slice nonSuffixA],
    mkSdsfxrevCase "false/prefix-is-not-suffix"
      #[.slice wholeA, .slice prefixA],
    mkSdsfxrevCase "false/suffix-longer-than-whole"
      #[.slice suffixA, .slice longerA],
    mkSdsfxrevCase "false/reversed-order"
      #[.slice suffixA, .slice wholeA]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkSdsfxrevCase "underflow/empty-stack" #[],
    mkSdsfxrevCase "underflow/one-item"
      #[.slice wholeA],
    mkSdsfxrevCase "type/top-not-slice"
      #[.slice wholeA, .null],
    mkSdsfxrevCase "type/second-not-slice"
      #[.null, .slice wholeA]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkSdsfxrevCase "gas/exact-cost-succeeds"
      #[.slice wholeA, .slice suffixA]
      #[.pushInt (.num sdsfxrevSetGasExact), .tonEnvOp .setGasLimit, sdsfxrevInstr],
    mkSdsfxrevCase "gas/exact-minus-one-out-of-gas"
      #[.slice wholeA, .slice suffixA]
      #[.pushInt (.num sdsfxrevSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdsfxrevInstr]
  ]

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 11 4) #[]

private def refsByCount (n : Nat) : Array Cell :=
  if n = 0 then #[]
  else if n = 1 then #[refLeafA]
  else if n = 2 then #[refLeafA, refLeafB]
  else if n = 3 then #[refLeafA, refLeafB, refLeafC]
  else #[refLeafA, refLeafB, refLeafC, refLeafD]

private def bitsBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickBitsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    let (idx, rng2) := randNat rng1 0 (bitsBoundaryPool.size - 1)
    (((bitsBoundaryPool[idx]?).getD 0), rng2)
  else
    randNat rng1 0 256

private def pickRefsMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 3
  if mode = 0 then
    (0, rng1)
  else if mode = 1 then
    (4, rng1)
  else
    randNat rng1 0 4

private def fuzzNoisePool : Array Value :=
  #[.null, intV 0, intV 7, intV (-9), .cell Cell.empty, .builder Builder.empty, .tuple #[], .cont (.quit 0)]

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (idx, rng1) := randNat rng0 0 (fuzzNoisePool.size - 1)
  (((fuzzNoisePool[idx]?).getD .null), rng1)

private def flipHeadBit (bs : BitString) : BitString :=
  if bs.isEmpty then
    bs
  else
    let b0 := (bs[0]?).getD false
    #[!b0] ++ bs.extract 1 bs.size

private def genSdsfxrevFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  if shape = 0 then
    let (wholeLen, rng2) := pickBitsMixed rng1
    let (wholeBits, rng3) := randBitString wholeLen rng2
    let (sufLen, rng4) := randNat rng3 0 wholeLen
    let sufBits := wholeBits.extract (wholeLen - sufLen) wholeLen
    let (wholeRefs, rng5) := pickRefsMixed rng4
    let (sufRefs, rng6) := pickRefsMixed rng5
    let whole := mkSliceWithBitsRefs wholeBits (refsByCount wholeRefs)
    let suf := mkSliceWithBitsRefs sufBits (refsByCount sufRefs)
    (mkSdsfxrevCase "fuzz/ok/suffix" #[.slice whole, .slice suf], rng6)
  else if shape = 1 then
    let (wholeLen0, rng2) := pickBitsMixed rng1
    let wholeLen : Nat := if wholeLen0 = 0 then 1 else wholeLen0
    let (wholeBits, rng3) := randBitString wholeLen rng2
    let (sufLen, rng4) := randNat rng3 1 wholeLen
    let sufBits := flipHeadBit (wholeBits.extract (wholeLen - sufLen) wholeLen)
    let whole := mkSliceWithBitsRefs wholeBits
    let suf := mkSliceWithBitsRefs sufBits
    (mkSdsfxrevCase "fuzz/false/mismatch" #[.slice whole, .slice suf], rng4)
  else if shape = 2 then
    let (wholeLen, rng2) := randNat rng1 0 128
    let (wholeBits, rng3) := randBitString wholeLen rng2
    let sufBits := wholeBits ++ #[true]
    (mkSdsfxrevCase "fuzz/false/longer" #[.slice (mkSliceWithBits wholeBits), .slice (mkSliceWithBits sufBits)], rng3)
  else if shape = 3 then
    (mkSdsfxrevCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 4 then
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdsfxrevCase "fuzz/underflow/one" #[noise], rng2)
  else if shape = 5 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdsfxrevCase "fuzz/type/top" #[.slice wholeA, bad], rng2)
  else if shape = 6 then
    let (bad, rng2) := pickNoiseValue rng1
    (mkSdsfxrevCase "fuzz/type/second" #[bad, .slice suffixA], rng2)
  else
    let (noise, rng2) := pickNoiseValue rng1
    (mkSdsfxrevCase "fuzz/ok/deep" #[noise, .slice wholeA, .slice suffixA], rng2)

def suite : InstrSuite where
  id := sdsfxrevId
  unit := #[
    mkUnitBoolCase "unit/ok/empty-suffix-on-nonempty" wholeA emptySlice (-1),
    mkUnitBoolCase "unit/ok/equal-length-equal-bits" wholeA wholeA (-1),
    mkUnitBoolCase "unit/ok/strict-suffix" wholeA suffixA (-1),
    mkUnitBoolCase "unit/false/non-suffix" wholeA nonSuffixA 0,
    mkUnitBoolCase "unit/false/prefix-is-not-suffix" wholeA prefixA 0,
    mkUnitBoolCase "unit/false/suffix-longer-than-whole" suffixA longerA 0,
    mkUnitBoolCase "unit/false/reversed-order" suffixA wholeA 0,
    mkUnitBoolCase "unit/ok/refs-ignored" wholeWithRefs suffixWithOtherRefs (-1),
    mkUnitBoolCase "unit/ok/deep-stack-preserved"
      wholeA suffixA (-1) #[intV 91, .null, .cell refLeafA],
    { name := "unit/ok/partial-whole-cursor"
      run := do
        let baseCell : Cell := Cell.mkOrdinary (stripeBits 18 0) #[refLeafA, refLeafB]
        let whole : Slice := { cell := baseCell, bitPos := 4, refPos := 1 }
        let rem := whole.readBits whole.bitsRemaining
        let suffixBits := rem.extract (rem.size - 6) rem.size
        let suffix : Slice := mkSliceWithBitsRefs suffixBits #[refLeafC]
        expectOkStack "partial-whole-cursor"
          (runSdsfxrevDirect #[.slice whole, .slice suffix])
          #[intV (-1)] }
    ,
    { name := "unit/ok/partial-suffix-cursor"
      run := do
        let suffixCell : Cell := Cell.mkOrdinary (stripeBits 17 1) #[refLeafA]
        let suffix : Slice := { cell := suffixCell, bitPos := 10, refPos := 0 }
        let wholeBits := stripeBits 5 0 ++ suffix.readBits suffix.bitsRemaining
        let whole : Slice := mkSliceWithBitsRefs wholeBits #[refLeafB, refLeafC]
        expectOkStack "partial-suffix-cursor"
          (runSdsfxrevDirect #[.slice whole, .slice suffix])
          #[intV (-1)] }
    ,
    { name := "unit/errors/underflow-type-and-order"
      run := do
        expectErr "underflow/empty"
          (runSdsfxrevDirect #[]) .stkUnd
        expectErr "underflow/single-nonslice-prioritizes-underflow"
          (runSdsfxrevDirect #[.null]) .stkUnd
        expectErr "type/top-not-slice"
          (runSdsfxrevDirect #[.slice wholeA, .null]) .typeChk
        expectErr "type/second-not-slice"
          (runSdsfxrevDirect #[.null, .slice wholeA]) .typeChk
        expectErr "type/both-not-slice"
          (runSdsfxrevDirect #[.cell refLeafA, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/decode-assembler-neighbors-and-gap"
      run := do
        let familyProgram : Array Instr := #[
          sdsfxInstr,
          sdsfxrevInstr,
          sdpsfxInstr,
          sdpsfxrevInstr,
          .add
        ]
        let familyCode ←
          match assembleCp0 familyProgram.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble family failed: {e}")
        let s0 := Slice.ofCell familyCode
        let s1 ← expectDecodeStep "decode/sdsfx" s0 sdsfxInstr 16
        let s2 ← expectDecodeStep "decode/sdsfxrev" s1 sdsfxrevInstr 16
        let s3 ← expectDecodeStep "decode/sdpsfx" s2 sdpsfxInstr 16
        let s4 ← expectDecodeStep "decode/sdpsfxrev" s3 sdpsfxrevInstr 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError
            s!"decode/family-end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        let singleCode ←
          match assembleCp0 [sdsfxrevInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if singleCode.bits = natToBits sdsfxrevOpcode 16 then
          pure ()
        else
          throw (IO.userError
            s!"opcode/sdsfxrev: expected 0xc70d encoding, got bits {singleCode.bits}")
        expectDecodeErr "decode/raw-gap-c706"
          (Slice.ofCell (Cell.mkOrdinary (natToBits 0xc706 16) #[]))
          .invOpcode }
    ,
    { name := "unit/dispatch/non-sdsfxrev-falls-through"
      run := do
        expectOkStack "dispatch/add"
          (runSdsfxrevDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/sdPfx"
          (runSdsfxrevDispatchFallback .sdPfx #[.slice wholeA, .slice prefixA])
          #[.slice wholeA, .slice prefixA, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-sdsfx"
          (runSdsfxrevDispatchFallback sdsfxInstr #[.slice wholeA, .slice suffixA])
          #[.slice wholeA, .slice suffixA, intV dispatchSentinel] }
  ]
  oracle := oracleSuccessCases ++ oracleFalseCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021124
      count := 500
      gen := genSdsfxrevFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDSFXREV
