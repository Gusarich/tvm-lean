import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDPSFX

/-
SDPSFX branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/Ext.lean` (`.sdPsfx`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`SDPSFX` encode: `0xc70e`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xc70e` decode to `.cellOp .sdPsfx`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`SDPSFX` registration)
  - `/Users/daniil/Coding/ton/crypto/vm/cells/CellSlice.cpp` (`is_proper_suffix_of`)

Branch map used for this suite:
- dispatch guard: only `.cellOp .sdPsfx` is handled by this suite's direct runner;
- stack checks: `checkUnderflow 2`, then pop top as `s2` and next as `s1`;
- predicate split: result is `-1` iff `s1.bitsRemaining < s2.bitsRemaining`
  and `s1` remaining bits are a suffix of `s2` remaining bits;
- references are ignored by suffix checks (bit content + cursor positions only).
-/

private def sdpsfxId : InstrId := { name := "SDPSFX" }

private def dispatchSentinel : Int := 50958

private def sdpsfxInstr : Instr := .cellOp .sdPsfx
private def sdsfxInstr : Instr := .cellOp .sdSfx
private def sdpsfxRevInstr : Instr := .cellOp .sdPsfxRev

private def execInstrCellOpSdPsfxOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp .sdPsfx => execCellOpExt .sdPsfx next
  | _ => next

private def execInstrCellOpExtAny (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpExt op next
  | _ => next

private def mkSdpsfxCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdpsfxInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdpsfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkSdpsfxProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdpsfxId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdpsfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpSdPsfxOnly sdpsfxInstr stack

private def runSdsfxDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpExtAny sdsfxInstr stack

private def runSdpsfxDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpSdPsfxOnly instr
    (VM.push (intV dispatchSentinel)) stack

private def sdpsfxSetGasExact : Int :=
  computeExactGasBudget sdpsfxInstr

private def sdpsfxSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdpsfxInstr

private def mkSliceWord (bits word : Nat) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsRefs (natToBits word bits) refs

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 3 2) #[]
private def refLeafC : Cell := Cell.mkOrdinary (natToBits 9 4) #[]

private def sEmpty : Slice := mkSliceWithBitsRefs #[]
private def sSuffix1_1 : Slice := mkSliceWord 1 1
private def sSuffix3_001 : Slice := mkSliceWord 3 1
private def sSuffix3_101 : Slice := mkSliceWord 3 5
private def sWhole1_1 : Slice := mkSliceWord 1 1
private def sWhole2_01 : Slice := mkSliceWord 2 1
private def sWhole6_110001 : Slice := mkSliceWord 6 49
private def sWhole6_110101 : Slice := mkSliceWord 6 53
private def sWhole6_111001 : Slice := mkSliceWord 6 57
private def sWhole8_35_refs : Slice := mkSliceWord 8 0x35 #[refLeafC]
private def sWhole8_c5 : Slice := mkSliceWord 8 0xC5

private def sSuffix3_101_refs : Slice := mkSliceWord 3 5 #[refLeafA, refLeafB]
private def sLen5_10101_refA : Slice := mkSliceWord 5 0x15 #[refLeafA]
private def sLen5_10101_refBC : Slice := mkSliceWord 5 0x15 #[refLeafB, refLeafC]

private def sLonger4_1001 : Slice := mkSliceWord 4 9
private def sShorter3_011 : Slice := mkSliceWord 3 3
private def sPrefix3_110 : Slice := mkSliceWord 3 6

private def suffix15Bits : BitString := stripeBits 15 1
private def whole31Bits : BitString := stripeBits 16 0 ++ suffix15Bits
private def suffix127Bits : BitString := stripeBits 127 0
private def whole255Bits : BitString := stripeBits 128 1 ++ suffix127Bits

private def sSuffix15 : Slice := mkSliceWithBitsRefs suffix15Bits
private def sWhole31 : Slice := mkSliceWithBitsRefs whole31Bits
private def sSuffix127 : Slice := mkSliceWithBitsRefs suffix127Bits
private def sWhole255 : Slice := mkSliceWithBitsRefs whole255Bits

private def partialCellOk : Cell :=
  Cell.mkOrdinary (natToBits 0x159 9) #[refLeafA, refLeafB]

private def partialSuffixOk : Slice :=
  { cell := partialCellOk, bitPos := 6, refPos := 1 }

private def partialWholeOk : Slice :=
  { cell := partialCellOk, bitPos := 2, refPos := 0 }

private def partialCellBad : Cell :=
  Cell.mkOrdinary (natToBits 0x6A 8) #[refLeafC]

private def partialSuffixBad : Slice :=
  { cell := partialCellOk, bitPos := 5, refPos := 0 }

private def partialWholeBad : Slice :=
  { cell := partialCellBad, bitPos := 1, refPos := 0 }

private def suffixLenBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 63, 127, 255]

private def suffixLenPositiveBoundaryPool : Array Nat :=
  #[1, 2, 3, 7, 8, 15, 16, 31, 63, 127, 255]

private def pickSuffixLenBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (suffixLenBoundaryPool.size - 1)
  (suffixLenBoundaryPool[idx]!, rng')

private def pickSuffixLenPositiveBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (suffixLenPositiveBoundaryPool.size - 1)
  (suffixLenPositiveBoundaryPool[idx]!, rng')

private def pickSuffixLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickSuffixLenBoundary rng1
  else
    randNat rng1 0 255

private def pickSuffixLenPositiveMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 4 then
    pickSuffixLenPositiveBoundary rng1
  else
    randNat rng1 1 255

private def pickPrefixLenMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 7
  if mode = 0 then
    (1, rng1)
  else if mode = 1 then
    (2, rng1)
  else if mode = 2 then
    (7, rng1)
  else if mode = 3 then
    (8, rng1)
  else
    randNat rng1 1 64

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let refs :=
    if pick = 0 then #[]
    else if pick = 1 then #[refLeafA]
    else if pick = 2 then #[refLeafA, refLeafB]
    else #[refLeafA, refLeafB, refLeafC]
  (refs, rng')

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else if pick = 2 then .cell refLeafA
    else .cell refLeafB
  (v, rng1)

private def mkProperSuffixSlices
    (suffixLen prefixLen phase : Nat)
    (suffixRefs : Array Cell := #[])
    (wholeRefs : Array Cell := #[]) : Slice × Slice :=
  let suffix := stripeBits suffixLen phase
  let pfx := stripeBits prefixLen (phase + 1)
  (mkSliceWithBitsRefs suffix suffixRefs, mkSliceWithBitsRefs (pfx ++ suffix) wholeRefs)

private def mkNonSuffixSlices (suffixLen prefixLen phase : Nat) : Slice × Slice :=
  let suffix := stripeBits suffixLen phase
  let badTail := stripeBits suffixLen (phase + 1)
  let pfx := stripeBits prefixLen phase
  (mkSliceWithBitsRefs suffix, mkSliceWithBitsRefs (pfx ++ badTail))

private def genSdpsfxFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 13
  if shape = 0 then
    let (suffixLen, rng2) := pickSuffixLenMixed rng1
    let (prefixLen, rng3) := pickPrefixLenMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (s1, s2) := mkProperSuffixSlices suffixLen prefixLen phase
    (mkSdpsfxCase s!"fuzz/ok/proper/suf-{suffixLen}/pre-{prefixLen}"
      #[.slice s1, .slice s2], rng4)
  else if shape = 1 then
    let (suffixLen, rng2) := pickSuffixLenMixed rng1
    let (prefixLen, rng3) := pickPrefixLenMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (refs1, rng5) := pickRefPack rng4
    let (refs2, rng6) := pickRefPack rng5
    let (s1, s2) := mkProperSuffixSlices suffixLen prefixLen phase refs1 refs2
    (mkSdpsfxCase s!"fuzz/ok/refs/suf-{suffixLen}/pre-{prefixLen}/r1-{refs1.size}/r2-{refs2.size}"
      #[.slice s1, .slice s2], rng6)
  else if shape = 2 then
    let (suffixLen, rng2) := pickSuffixLenMixed rng1
    let (prefixLen, rng3) := pickPrefixLenMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (noise, rng5) := pickNoise rng4
    let (s1, s2) := mkProperSuffixSlices suffixLen prefixLen phase
    (mkSdpsfxCase s!"fuzz/ok/deep/suf-{suffixLen}/pre-{prefixLen}"
      #[noise, .slice s1, .slice s2], rng5)
  else if shape = 3 then
    let (len, rng2) := pickSuffixLenMixed rng1
    let (phase, rng3) := randNat rng2 0 1
    let (refs, rng4) := pickRefPack rng3
    let s := mkSliceWithBitsRefs (stripeBits len phase) refs
    (mkSdpsfxCase s!"fuzz/false/equal/sz-{len}/refs-{refs.size}"
      #[.slice s, .slice s], rng4)
  else if shape = 4 then
    let (suffixLen, rng2) := pickSuffixLenPositiveMixed rng1
    let (prefixLen, rng3) := pickPrefixLenMixed rng2
    let (phase, rng4) := randNat rng3 0 1
    let (s1, s2) := mkNonSuffixSlices suffixLen prefixLen phase
    (mkSdpsfxCase s!"fuzz/false/non-suffix/suf-{suffixLen}/pre-{prefixLen}"
      #[.slice s1, .slice s2], rng4)
  else if shape = 5 then
    let (len2, rng2) := pickSuffixLenMixed rng1
    let (delta, rng3) := randNat rng2 1 24
    let (phase, rng4) := randNat rng3 0 1
    let s1 := mkSliceWithBitsRefs (stripeBits (len2 + delta) phase)
    let s2 := mkSliceWithBitsRefs (stripeBits len2 (phase + 1))
    (mkSdpsfxCase s!"fuzz/false/longer-first/s1-{len2 + delta}/s2-{len2}"
      #[.slice s1, .slice s2], rng4)
  else if shape = 6 then
    let (len, rng2) := pickSuffixLenPositiveMixed rng1
    let (phase, rng3) := randNat rng2 0 1
    let s1 := mkSliceWithBitsRefs (stripeBits len phase)
    (mkSdpsfxCase s!"fuzz/false/nonempty-vs-empty/s1-{len}"
      #[.slice s1, .slice sEmpty], rng3)
  else if shape = 7 then
    (mkSdpsfxCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 8 then
    (mkSdpsfxCase "fuzz/underflow/one-item" #[.slice sSuffix3_101], rng1)
  else if shape = 9 then
    (mkSdpsfxCase "fuzz/type/top-not-slice" #[.slice sSuffix3_101, .null], rng1)
  else if shape = 10 then
    (mkSdpsfxCase "fuzz/type/second-not-slice" #[.null, .slice sWhole6_110101], rng1)
  else if shape = 11 then
    (mkSdpsfxCase "fuzz/gas/exact"
      #[.slice sSuffix3_101, .slice sWhole6_110101]
      #[.pushInt (.num sdpsfxSetGasExact), .tonEnvOp .setGasLimit, sdpsfxInstr], rng1)
  else if shape = 12 then
    (mkSdpsfxCase "fuzz/gas/exact-minus-one"
      #[.slice sSuffix3_101, .slice sWhole6_110101]
      #[.pushInt (.num sdpsfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdpsfxInstr], rng1)
  else
    (mkSdpsfxCase "fuzz/false/same-len-diff-refs"
      #[.slice sLen5_10101_refA, .slice sLen5_10101_refBC], rng1)

def suite : InstrSuite where
  id := sdpsfxId
  unit := #[
    { name := "unit/direct/success-proper-suffix"
      run := do
        expectOkStack "ok/basic-3-in-6"
          (runSdpsfxDirect #[.slice sSuffix3_101, .slice sWhole6_110101])
          #[intV (-1)]
        expectOkStack "ok/basic-1-in-2"
          (runSdpsfxDirect #[.slice sSuffix1_1, .slice sWhole2_01])
          #[intV (-1)]
        expectOkStack "ok/empty-is-proper-suffix-of-nonempty"
          (runSdpsfxDirect #[.slice sEmpty, .slice sWhole8_c5])
          #[intV (-1)]
        expectOkStack "ok/refs-ignored-for-suffix"
          (runSdpsfxDirect #[.slice sSuffix3_101_refs, .slice sWhole8_35_refs])
          #[intV (-1)]
        expectOkStack "ok/partial-cursor-suffix"
          (runSdpsfxDirect #[.slice partialSuffixOk, .slice partialWholeOk])
          #[intV (-1)]
        expectOkStack "ok/deep-stack-preserve-below"
          (runSdpsfxDirect #[.null, .cell refLeafA, .slice sSuffix3_101, .slice sWhole6_110101])
          #[.null, .cell refLeafA, intV (-1)] }
    ,
    { name := "unit/direct/failure-returns-zero"
      run := do
        expectOkStack "false/equal-nonempty"
          (runSdpsfxDirect #[.slice sWhole6_110101, .slice sWhole6_110101])
          #[intV 0]
        expectOkStack "false/equal-empty"
          (runSdpsfxDirect #[.slice sEmpty, .slice sEmpty])
          #[intV 0]
        expectOkStack "false/not-a-suffix"
          (runSdpsfxDirect #[.slice sSuffix3_101, .slice sWhole6_111001])
          #[intV 0]
        expectOkStack "false/longer-first"
          (runSdpsfxDirect #[.slice sLonger4_1001, .slice sShorter3_011])
          #[intV 0]
        expectOkStack "false/prefix-not-suffix"
          (runSdpsfxDirect #[.slice sPrefix3_110, .slice sWhole6_110001])
          #[intV 0]
        expectOkStack "false/nonempty-vs-empty"
          (runSdpsfxDirect #[.slice sSuffix1_1, .slice sEmpty])
          #[intV 0]
        expectOkStack "false/same-len-diff-refs"
          (runSdpsfxDirect #[.slice sLen5_10101_refA, .slice sLen5_10101_refBC])
          #[intV 0]
        expectOkStack "false/partial-cursor-mismatch"
          (runSdpsfxDirect #[.slice partialSuffixBad, .slice partialWholeBad])
          #[intV 0] }
    ,
    { name := "unit/direct/proper-vs-nonproper-distinction"
      run := do
        expectOkStack "sdpsfx/equal-slices-not-proper"
          (runSdpsfxDirect #[.slice sWhole6_110101, .slice sWhole6_110101])
          #[intV 0]
        expectOkStack "sdsfx/equal-slices-allowed"
          (runSdsfxDirect #[.slice sWhole6_110101, .slice sWhole6_110101])
          #[intV (-1)]
        expectOkStack "sdpsfx/proper-suffix-true"
          (runSdpsfxDirect #[.slice sSuffix3_101, .slice sWhole6_110101])
          #[intV (-1)]
        expectOkStack "sdsfx/proper-suffix-true"
          (runSdsfxDirect #[.slice sSuffix3_101, .slice sWhole6_110101])
          #[intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runSdpsfxDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSdpsfxDirect #[.slice sSuffix3_101]) .stkUnd
        expectErr "type/top-not-slice-null"
          (runSdpsfxDirect #[.slice sSuffix3_101, .null]) .typeChk
        expectErr "type/top-not-slice-int"
          (runSdpsfxDirect #[.slice sSuffix3_101, intV 7]) .typeChk
        expectErr "type/second-not-slice"
          (runSdpsfxDirect #[.null, .slice sWhole6_110101]) .typeChk
        expectErr "type/order-top-first"
          (runSdpsfxDirect #[intV 7, .null]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let single ←
          match assembleCp0 [sdpsfxInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble single failed: {e}")
        if single.bits.extract 0 16 = natToBits 0xc70e 16 then
          pure ()
        else
          throw (IO.userError "encode/sdpsfx-opcode: expected 0xc70e")

        let program : Array Instr := #[sdsfxInstr, sdpsfxInstr, sdpsfxRevInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble program failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdsfx-neighbor" s0 sdsfxInstr 16
        let s2 ← expectDecodeStep "decode/sdpsfx" s1 sdpsfxInstr 16
        let s3 ← expectDecodeStep "decode/sdpsfxrev-neighbor" s2 sdpsfxRevInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-sdpsfx-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop"
          (runSdpsfxDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/neighbor-cellop-sdsfx"
          (runSdpsfxDispatchFallback sdsfxInstr #[.slice sSuffix3_101, .slice sWhole6_110101])
          #[.slice sSuffix3_101, .slice sWhole6_110101, intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdpsfxCase "ok/basic-3-in-6"
      #[.slice sSuffix3_101, .slice sWhole6_110101],
    mkSdpsfxCase "ok/basic-1-in-2"
      #[.slice sSuffix1_1, .slice sWhole2_01],
    mkSdpsfxCase "ok/empty-in-1bit"
      #[.slice sEmpty, .slice sWhole1_1],
    mkSdpsfxCase "ok/empty-in-8bit"
      #[.slice sEmpty, .slice sWhole8_c5],
    mkSdpsfxCase "ok/refs-ignored"
      #[.slice sSuffix3_101_refs, .slice sWhole8_35_refs],
    mkSdpsfxCase "ok/deep-stack-preserve-null"
      #[.null, .slice sSuffix3_101, .slice sWhole6_110101],
    mkSdpsfxCase "ok/deep-stack-preserve-cell-int"
      #[.cell refLeafA, intV (-9), .slice sSuffix1_1, .slice sWhole2_01],
    mkSdpsfxCase "ok/long-15-in-31"
      #[.slice sSuffix15, .slice sWhole31],
    mkSdpsfxCase "ok/long-127-in-255"
      #[.slice sSuffix127, .slice sWhole255],
    mkSdpsfxCase "ok/leading-zeros-suffix"
      #[.slice sSuffix3_001, .slice sWhole6_110001],

    mkSdpsfxCase "false/equal-nonempty"
      #[.slice sWhole6_110101, .slice sWhole6_110101],
    mkSdpsfxCase "false/equal-empty"
      #[.slice sEmpty, .slice sEmpty],
    mkSdpsfxCase "false/non-suffix-3-in-6"
      #[.slice sSuffix3_101, .slice sWhole6_111001],
    mkSdpsfxCase "false/longer-first"
      #[.slice sLonger4_1001, .slice sShorter3_011],
    mkSdpsfxCase "false/prefix-not-suffix"
      #[.slice sPrefix3_110, .slice sWhole6_110001],
    mkSdpsfxCase "false/nonempty-vs-empty"
      #[.slice sSuffix1_1, .slice sEmpty],
    mkSdpsfxCase "false/same-len-diff-refs"
      #[.slice sLen5_10101_refA, .slice sLen5_10101_refBC],
    mkSdpsfxCase "false/deep-stack-preserve-int"
      #[intV 42, .slice sSuffix3_101, .slice sWhole6_111001],

    mkSdpsfxCase "underflow/empty" #[],
    mkSdpsfxCase "underflow/one-item" #[.slice sSuffix3_101],
    mkSdpsfxCase "type/top-not-slice" #[.slice sSuffix3_101, .null],
    mkSdpsfxCase "type/second-not-slice" #[.null, .slice sWhole6_110101],

    mkSdpsfxProgramCase "gas/exact-cost-succeeds"
      #[.slice sSuffix3_101, .slice sWhole6_110101]
      #[.pushInt (.num sdpsfxSetGasExact), .tonEnvOp .setGasLimit, sdpsfxInstr],
    mkSdpsfxProgramCase "gas/exact-minus-one-out-of-gas"
      #[.slice sSuffix3_101, .slice sWhole6_110101]
      #[.pushInt (.num sdpsfxSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdpsfxInstr]
  ]
  fuzz := #[
    { seed := 2026021026
      count := 500
      gen := genSdpsfxFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDPSFX
