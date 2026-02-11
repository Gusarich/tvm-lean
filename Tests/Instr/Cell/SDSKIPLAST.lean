import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.SDSKIPLAST

/-
SDSKIPLAST branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cell/Sdskiplast.lean` (`.sdskiplast`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (encode `0xd723`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode `0xd723`)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`SDSKIPLAST` via `exec_slice_op_args(... cs.skip_last(bits))`).

Branch map used for this suite:
- dispatch guard: `.sdskiplast` executes, all other instructions fall through to `next`;
- pre-check: `checkUnderflow 2` before any pop/type/range checks;
- `popNatUpTo 1023` split: `typeChk` (non-int), `rangeChk` (nan/negative/>1023), success;
- second pop split: `popSlice` success vs `typeChk`;
- core semantics split:
  `bits ≤ s.bitsRemaining` -> keep leading `s.bitsRemaining - bits` bits,
  keep all remaining refs (`refPos .. end`);
  otherwise -> `cellUnd`;
- opcode/decode boundary around `0xd720..0xd724`, plus near family `0xd733`.
-/

private def sdskiplastId : InstrId := { name := "SDSKIPLAST" }

private def sdskiplastInstr : Instr := .sdskiplast
private def sdcutfirstInstr : Instr := .sdcutfirst
private def sdskipfirstInstr : Instr := .sdskipfirst
private def sdcutlastInstr : Instr := .sdcutlast
private def sdsubstrInstr : Instr := .cellOp .sdSubstr
private def sskiplastInstr : Instr := .cellOp .sskiplast

private def dispatchSentinel : Int := 5723

private def sdcutfirstOpcode : Nat := 0xd720
private def sdskipfirstOpcode : Nat := 0xd721
private def sdcutlastOpcode : Nat := 0xd722
private def sdskiplastOpcode : Nat := 0xd723
private def sdsubstrOpcode : Nat := 0xd724
private def sskiplastOpcode : Nat := 0xd733

private def mkSdskiplastCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sdskiplastInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sdskiplastId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runSdskiplastDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellSdskiplast sdskiplastInstr stack

private def runSdskiplastDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellSdskiplast instr (VM.push (intV dispatchSentinel)) stack

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

private def mkSliceCursor
    (bits : BitString)
    (refs : Array Cell)
    (bitPos refPos : Nat) : Slice :=
  { cell := Cell.mkOrdinary bits refs, bitPos := bitPos, refPos := refPos }

private def refLeafD : Cell := Cell.mkOrdinary (natToBits 0x2d 6) #[]

private def emptySlice : Slice := mkSliceWithBitsRefs #[]

private def bits8A5 : BitString := natToBits 0xa5 8
private def slice8Refs2 : Slice := mkSliceWithBitsRefs bits8A5 #[refLeafA, refLeafB]

private def bits256Stripe : BitString := stripeBits 256 1
private def slice256Refs1 : Slice := mkSliceWithBitsRefs bits256Stripe #[refLeafC]

private def bits1023Stripe : BitString := stripeBits 1023 0
private def slice1023Refs4 : Slice :=
  mkSliceWithBitsRefs bits1023Stripe #[refLeafA, refLeafB, refLeafC, refLeafD]

private def cursorBits : BitString := natToBits 0x2d5 10 ++ natToBits 0x53 7
private def cursorRefs : Array Cell := #[refLeafA, refLeafB, refLeafC]
private def cursorSlice : Slice := mkSliceCursor cursorBits cursorRefs 4 1

private def edgeCell : Cell :=
  Cell.mkOrdinary (natToBits 0x11b 9) #[refLeafA, refLeafB]

private def edgeCursorA : Slice := { cell := edgeCell, bitPos := 1, refPos := 0 }
private def edgeCursorB : Slice := { cell := edgeCell, bitPos := 8, refPos := 1 }

private def popNatUpToModel (v : Value) (max : Nat := 1023) : Except Excno Nat :=
  match v with
  | .int .nan => .error .rangeChk
  | .int (.num n) =>
      if n < 0 then
        .error .rangeChk
      else
        let u := n.toNat
        if u > max then
          .error .rangeChk
        else
          .ok u
  | _ => .error .typeChk

private def mkSdskiplastOutSlice (s : Slice) (dropBits : Nat) : Slice :=
  let keepBits : Nat := s.bitsRemaining - dropBits
  let newCell : Cell :=
    Cell.mkOrdinary
      (s.cell.bits.extract s.bitPos (s.bitPos + keepBits))
      (s.cell.refs.extract s.refPos s.cell.refs.size)
  Slice.ofCell newCell

private def runSdskiplastModel (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size < 2 then
    throw .stkUnd
  let top := stack.back!
  let withoutTop := stack.extract 0 (stack.size - 1)
  let bits ← popNatUpToModel top 1023
  let second := withoutTop.back!
  let below := withoutTop.extract 0 (withoutTop.size - 1)
  let s ←
    match second with
    | .slice s => pure s
    | _ => throw .typeChk
  if bits ≤ s.bitsRemaining then
    pure (below.push (.slice (mkSdskiplastOutSlice s bits)))
  else
    throw .cellUnd

private def sdskiplastSetGasExact : Int :=
  computeExactGasBudget sdskiplastInstr

private def sdskiplastSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne sdskiplastInstr

private def lenPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 511, 512, 1022, 1023]

private def pickLen (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (lenPool.size - 1)
  (lenPool[idx]!, rng')

private def pickRefPack (rng : StdGen) : Array Cell × StdGen :=
  let (pick, rng') := randNat rng 0 4
  let refs :=
    if pick = 0 then #[]
    else if pick = 1 then #[refLeafA]
    else if pick = 2 then #[refLeafA, refLeafB]
    else if pick = 3 then #[refLeafA, refLeafB, refLeafC]
    else #[refLeafA, refLeafB, refLeafC, refLeafD]
  (refs, rng')

private def pickNonIntNonSlice (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  let v : Value :=
    if pick = 0 then .null
    else .cell refLeafA
  (v, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 77
    else .cell refLeafB
  (v, rng')

private def genSdskiplastFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 11
  if shape = 0 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let (refs, rng4) := pickRefPack rng3
    let s := mkSliceWithBitsRefs (stripeBits len phase) refs
    (mkSdskiplastCase s!"fuzz/ok/drop-0/len-{len}/refs-{refs.size}"
      #[.slice s, intV 0], rng4)
  else if shape = 1 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let (refs, rng4) := pickRefPack rng3
    let s := mkSliceWithBitsRefs (stripeBits len phase) refs
    (mkSdskiplastCase s!"fuzz/ok/drop-all/len-{len}/refs-{refs.size}"
      #[.slice s, intV (Int.ofNat len)], rng4)
  else if shape = 2 then
    let (len, rng2) := randNat rng1 1 1023
    let (drop, rng3) := randNat rng2 0 len
    let (phase, rng4) := randNat rng3 0 1
    let (refs, rng5) := pickRefPack rng4
    let s := mkSliceWithBitsRefs (stripeBits len phase) refs
    (mkSdskiplastCase s!"fuzz/ok/drop-some/len-{len}/drop-{drop}"
      #[.slice s, intV (Int.ofNat drop)], rng5)
  else if shape = 3 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let (refs, rng4) := pickRefPack rng3
    let (drop, rng5) := randNat rng4 0 len
    let (noise1, rng6) := pickNoise rng5
    let (noise2, rng7) := pickNoise rng6
    let s := mkSliceWithBitsRefs (stripeBits len phase) refs
    (mkSdskiplastCase s!"fuzz/ok/deep/len-{len}/drop-{drop}"
      #[noise1, noise2, .slice s, intV (Int.ofNat drop)], rng7)
  else if shape = 4 then
    let (len, rng2) := randNat rng1 0 1022
    let (phase, rng3) := randNat rng2 0 1
    let s := mkSliceWithBitsRefs (stripeBits len phase)
    (mkSdskiplastCase s!"fuzz/err/cellund/len-{len}/drop-{len + 1}"
      #[.slice s, intV (Int.ofNat (len + 1))], rng3)
  else if shape = 5 then
    (mkSdskiplastCase "fuzz/err/underflow-empty" #[], rng1)
  else if shape = 6 then
    let (pick, rng2) := randNat rng1 0 1
    if pick = 0 then
      (mkSdskiplastCase "fuzz/err/underflow-one-int" #[intV 0], rng2)
    else
      (mkSdskiplastCase "fuzz/err/underflow-one-slice"
        #[.slice (mkSliceWithBitsRefs (stripeBits 8 0))], rng2)
  else if shape = 7 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let (badTop, rng4) := pickNonIntNonSlice rng3
    let s := mkSliceWithBitsRefs (stripeBits len phase)
    (mkSdskiplastCase s!"fuzz/err/type-top-not-int/len-{len}"
      #[.slice s, badTop], rng4)
  else if shape = 8 then
    let (badSecond, rng2) := pickNonIntNonSlice rng1
    let (drop, rng3) := randNat rng2 0 1023
    (mkSdskiplastCase s!"fuzz/err/type-second-not-slice/drop-{drop}"
      #[badSecond, intV (Int.ofNat drop)], rng3)
  else if shape = 9 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let s := mkSliceWithBitsRefs (stripeBits len phase)
    (mkSdskiplastCase s!"fuzz/err/range-negative/len-{len}"
      #[.slice s, intV (-1)], rng3)
  else if shape = 10 then
    let (len, rng2) := pickLen rng1
    let (phase, rng3) := randNat rng2 0 1
    let s := mkSliceWithBitsRefs (stripeBits len phase)
    (mkSdskiplastCase s!"fuzz/err/range-over1023/len-{len}"
      #[.slice s, intV 1024], rng3)
  else
    let (badSecond, rng2) := pickNonIntNonSlice rng1
    (mkSdskiplastCase "fuzz/err/range-before-second-type"
      #[badSecond, intV 1024], rng2)

def suite : InstrSuite where
  id := sdskiplastId
  unit := #[
    { name := "unit/direct/success-full-slice-boundaries"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("empty/drop0", emptySlice, 0),
            ("len8/drop0", slice8Refs2, 0),
            ("len8/drop1", slice8Refs2, 1),
            ("len8/drop8", slice8Refs2, 8),
            ("len256/drop255", slice256Refs1, 255),
            ("len256/drop256", slice256Refs1, 256),
            ("len1023/drop0", slice1023Refs4, 0),
            ("len1023/drop1023", slice1023Refs4, 1023)
          ]
        for (label, s, drop) in checks do
          expectOkStack label
            (runSdskiplastDirect #[.slice s, intV (Int.ofNat drop)])
            #[.slice (mkSdskiplastOutSlice s drop)] }
    ,
    { name := "unit/direct/partial-cursor-semantics"
      run := do
        let checks : Array (String × Slice × Nat) :=
          #[
            ("cursor/drop0", cursorSlice, 0),
            ("cursor/drop3", cursorSlice, 3),
            ("cursor/drop-all", cursorSlice, cursorSlice.bitsRemaining),
            ("edge-a/drop4", edgeCursorA, 4),
            ("edge-b/drop1", edgeCursorB, 1)
          ]
        for (label, s, drop) in checks do
          expectOkStack label
            (runSdskiplastDirect #[.slice s, intV (Int.ofNat drop)])
            #[.slice (mkSdskiplastOutSlice s drop)] }
    ,
    { name := "unit/direct/deep-stack-preserved"
      run := do
        expectOkStack "deep/null-int-cell"
          (runSdskiplastDirect #[.null, intV 17, .cell refLeafA, .slice slice8Refs2, intV 1])
          #[.null, intV 17, .cell refLeafA, .slice (mkSdskiplastOutSlice slice8Refs2 1)]

        expectOkStack "deep/builder-cursor"
          (runSdskiplastDirect #[.builder Builder.empty, .slice cursorSlice, intV 2])
          #[.builder Builder.empty, .slice (mkSdskiplastOutSlice cursorSlice 2)] }
    ,
    { name := "unit/direct/errors-underflow-type-range-cellund"
      run := do
        expectErr "underflow/empty"
          (runSdskiplastDirect #[]) .stkUnd
        expectErr "underflow/one-int"
          (runSdskiplastDirect #[intV 0]) .stkUnd
        expectErr "underflow/one-slice"
          (runSdskiplastDirect #[.slice slice8Refs2]) .stkUnd

        expectErr "type/top-null-not-int"
          (runSdskiplastDirect #[.slice slice8Refs2, .null]) .typeChk
        expectErr "type/top-cell-not-int"
          (runSdskiplastDirect #[.slice slice8Refs2, .cell refLeafA]) .typeChk
        expectErr "type/second-not-slice"
          (runSdskiplastDirect #[.null, intV 0]) .typeChk

        expectErr "range/top-nan"
          (runSdskiplastDirect #[.slice slice8Refs2, .int .nan]) .rangeChk
        expectErr "range/top-negative"
          (runSdskiplastDirect #[.slice slice8Refs2, intV (-1)]) .rangeChk
        expectErr "range/top-over-1023"
          (runSdskiplastDirect #[.slice slice8Refs2, intV 1024]) .rangeChk
        expectErr "range/precedes-second-type"
          (runSdskiplastDirect #[.null, intV 1024]) .rangeChk

        expectErr "cellund/drop-more-than-remaining"
          (runSdskiplastDirect #[.slice (mkSliceWithBitsRefs (stripeBits 7 0)), intV 8]) .cellUnd }
    ,
    { name := "unit/model/alignment-representative-stacks"
      run := do
        let samples : Array (String × Array Value) :=
          #[
            ("ok/empty-drop0", #[.slice emptySlice, intV 0]),
            ("ok/len8-drop1", #[.slice slice8Refs2, intV 1]),
            ("ok/len8-drop8", #[.slice slice8Refs2, intV 8]),
            ("ok/cursor-drop2", #[.slice cursorSlice, intV 2]),
            ("ok/deep", #[.null, .slice slice256Refs1, intV 255]),
            ("err/underflow", #[]),
            ("err/type-top", #[.slice slice8Refs2, .null]),
            ("err/type-second", #[.null, intV 0]),
            ("err/range-negative", #[.slice slice8Refs2, intV (-1)]),
            ("err/range-nan", #[.slice slice8Refs2, .int .nan]),
            ("err/range-over", #[.slice slice8Refs2, intV 1024]),
            ("err/cellund", #[.slice (mkSliceWithBitsRefs (stripeBits 3 0)), intV 4])
          ]
        for (label, stack) in samples do
          expectSameOutcome label
            (runSdskiplastDirect stack)
            (runSdskiplastModel stack) }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let single ←
          match assembleCp0 [sdskiplastInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sdskiplast failed: {e}")
        if single.bits = natToBits sdskiplastOpcode 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdskiplast: expected 0xd723, got bits {single.bits}")
        if single.bits.size = 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/sdskiplast: expected 16 bits, got {single.bits.size}")

        let prog : Array Instr :=
          #[sdcutfirstInstr, sdskipfirstInstr, sdcutlastInstr, sdskiplastInstr, sdsubstrInstr, .add]
        let code ←
          match assembleCp0 prog.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/sdcutfirst" s0 sdcutfirstInstr 16
        let s2 ← expectDecodeStep "decode/sdskipfirst" s1 sdskipfirstInstr 16
        let s3 ← expectDecodeStep "decode/sdcutlast" s2 sdcutlastInstr 16
        let s4 ← expectDecodeStep "decode/sdskiplast" s3 sdskiplastInstr 16
        let s5 ← expectDecodeStep "decode/sdsubstr" s4 sdsubstrInstr 16
        let s6 ← expectDecodeStep "decode/add-tail" s5 .add 8
        if s6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s6.bitsRemaining} bits remaining")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits sdcutfirstOpcode 16 ++
          natToBits sdskipfirstOpcode 16 ++
          natToBits sdcutlastOpcode 16 ++
          natToBits sdskiplastOpcode 16 ++
          natToBits sdsubstrOpcode 16 ++
          natToBits sskiplastOpcode 16 ++
          addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-sdcutfirst" r0 sdcutfirstInstr 16
        let r2 ← expectDecodeStep "decode/raw-sdskipfirst" r1 sdskipfirstInstr 16
        let r3 ← expectDecodeStep "decode/raw-sdcutlast" r2 sdcutlastInstr 16
        let r4 ← expectDecodeStep "decode/raw-sdskiplast" r3 sdskiplastInstr 16
        let r5 ← expectDecodeStep "decode/raw-sdsubstr" r4 sdsubstrInstr 16
        let r6 ← expectDecodeStep "decode/raw-sskiplast" r5 sskiplastInstr 16
        let r7 ← expectDecodeStep "decode/raw-add-tail" r6 .add 8
        if r7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r7.bitsRemaining} bits remaining")

        let trunc := (natToBits sdskiplastOpcode 16).extract 0 15
        expectDecodeErr "decode/truncated-opcode" (mkSliceFromBits trunc) .invOpcode }
    ,
    { name := "unit/dispatch/non-sdskiplast-falls-through"
      run := do
        expectOkStack "dispatch/sdcutlast"
          (runSdskiplastDispatchFallback sdcutlastInstr #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/cellop-sskiplast"
          (runSdskiplastDispatchFallback sskiplastInstr #[intV 9])
          #[intV 9, intV dispatchSentinel]
        expectOkStack "dispatch/add"
          (runSdskiplastDispatchFallback .add #[])
          #[intV dispatchSentinel] }
  ]
  oracle := #[
    mkSdskiplastCase "ok/drop0-empty"
      #[.slice emptySlice, intV 0],
    mkSdskiplastCase "ok/drop0-len8-refs2"
      #[.slice slice8Refs2, intV 0],
    mkSdskiplastCase "ok/drop1-len8-refs2"
      #[.slice slice8Refs2, intV 1],
    mkSdskiplastCase "ok/drop7-len8"
      #[.slice slice8Refs2, intV 7],
    mkSdskiplastCase "ok/drop8-len8-to-empty"
      #[.slice slice8Refs2, intV 8],
    mkSdskiplastCase "ok/drop255-len256"
      #[.slice slice256Refs1, intV 255],
    mkSdskiplastCase "ok/drop256-len256-to-empty"
      #[.slice slice256Refs1, intV 256],
    mkSdskiplastCase "ok/drop1022-len1023"
      #[.slice slice1023Refs4, intV 1022],
    mkSdskiplastCase "ok/drop1023-len1023-to-empty"
      #[.slice slice1023Refs4, intV 1023],
    mkSdskiplastCase "ok/deep-preserve-null"
      #[.null, .slice slice8Refs2, intV 1],
    mkSdskiplastCase "ok/deep-preserve-two-values"
      #[.cell refLeafD, intV (-8), .slice slice256Refs1, intV 64],

    mkSdskiplastCase "underflow/empty" #[],
    mkSdskiplastCase "underflow/one-int" #[intV 0],
    mkSdskiplastCase "underflow/one-slice" #[.slice slice8Refs2],
    mkSdskiplastCase "type/top-not-int-null"
      #[.slice slice8Refs2, .null],
    mkSdskiplastCase "type/top-not-int-cell"
      #[.slice slice8Refs2, .cell refLeafA],
    mkSdskiplastCase "type/second-not-slice-null"
      #[.null, intV 0],
    mkSdskiplastCase "range/top-negative"
      #[.slice slice8Refs2, intV (-1)],
    mkSdskiplastCase "range/top-over-1023"
      #[.slice slice8Refs2, intV 1024],
    mkSdskiplastCase "range/order-before-second-type"
      #[.null, intV 1024],
    mkSdskiplastCase "cellund/drop-more-than-remaining"
      #[.slice (mkSliceWithBitsRefs (stripeBits 6 0) #[refLeafB]), intV 7],

    mkSdskiplastCase "gas/exact-cost-succeeds"
      #[.slice slice8Refs2, intV 1]
      #[.pushInt (.num sdskiplastSetGasExact), .tonEnvOp .setGasLimit, sdskiplastInstr],
    mkSdskiplastCase "gas/exact-minus-one-out-of-gas"
      #[.slice slice8Refs2, intV 1]
      #[.pushInt (.num sdskiplastSetGasExactMinusOne), .tonEnvOp .setGasLimit, sdskiplastInstr]
  ]
  fuzz := #[
    { seed := 2026021016
      count := 120
      gen := genSdskiplastFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.SDSKIPLAST
