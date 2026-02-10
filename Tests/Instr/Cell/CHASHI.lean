import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CHASHI

/-
CHASHI branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/ChashI.lean`
  - `TvmLean/Semantics/Exec/CellOp.lean` (dispatch chain for `.cellOp`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`0xd768..0xd76b`, arg `i=0..3`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xd768..0xd76b` decode family)
- C++ authoritative file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (`exec_cell_hash_i`)

Branch map covered by this suite:
- dispatch gate (`.cellOp (.chashI i)` vs fallthrough to `next`);
- stack failures from `popCell` (underflow + strict top-type);
- `computeLevelInfo?` failure path mapped to `cellUnd`;
- hash selection by immediate level `i` and level clamping via `CellLevelInfo.getHash`;
- opcode/decoder boundaries around `0xd768..0xd76b` with neighboring opcodes.
-/

private def chashIId : InstrId := { name := "CHASHI" }

private def dispatchSentinel : Int := 768

private def chashIInstr (i : Nat) : Instr :=
  .cellOp (.chashI i)

private def chashIWord (i : Nat) : Nat :=
  0xd768 + i

private def execInstrCellOpChashIOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpChashI op next
  | _ => next

private def mkChashICase
    (name : String)
    (i : Nat)
    (stack : Array Value)
    (program : Array Instr := #[chashIInstr i])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := chashIId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runChashIDirect (i : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpChashIOnly (chashIInstr i) stack

private def runChashIDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpChashIOnly instr (VM.push (intV dispatchSentinel)) stack

private def bytesToBitsBE (bytes : Array UInt8) : BitString :=
  bytes.foldl (init := #[]) (fun acc b => acc ++ natToBits b.toNat 8)

private def mkHashBytes32 (base : Nat) (step : Nat) : Array UInt8 :=
  Array.ofFn (n := 32) fun i =>
    UInt8.ofNat ((base + i.1 * step) &&& 0xff)

private def depthBytesBE2 (d : Nat) : Array UInt8 :=
  #[UInt8.ofNat ((d >>> 8) &&& 0xff), UInt8.ofNat (d &&& 0xff)]

private def mkPrunedMask1Cell (h0 : Array UInt8) (d0 : Nat) : Cell :=
  let bytes : Array UInt8 :=
    #[UInt8.ofNat 1, UInt8.ofNat 1] ++ h0 ++ depthBytesBE2 d0
  { bits := bytesToBitsBE bytes
    refs := #[]
    special := true
    levelMask := 1 }

private def mkPrunedMask7Cell
    (h0 h1 h2 : Array UInt8)
    (d0 d1 d2 : Nat) : Cell :=
  let bytes : Array UInt8 :=
    #[UInt8.ofNat 1, UInt8.ofNat 7]
      ++ h0 ++ h1 ++ h2
      ++ depthBytesBE2 d0 ++ depthBytesBE2 d1 ++ depthBytesBE2 d2
  { bits := bytesToBitsBE bytes
    refs := #[]
    special := true
    levelMask := 7 }

private def leafA : Cell := Cell.ofUInt 8 0xa5
private def leafB : Cell := Cell.mkOrdinary (natToBits 3 2) #[]

private def ordLeaf : Cell := Cell.mkOrdinary (natToBits 0x155 9) #[]
private def ordOneRef : Cell := Cell.mkOrdinary (natToBits 0x2a 6) #[leafA]
private def ordTwoRefs : Cell := Cell.mkOrdinary (natToBits 0xface 16) #[leafA, leafB]
private def ordDeep : Cell := Cell.mkOrdinary (natToBits 0x33 6) #[ordOneRef, ordTwoRefs]

private def prunedHashA : Array UInt8 := mkHashBytes32 0x11 3
private def prunedHashB : Array UInt8 := mkHashBytes32 0x55 5
private def prunedHashC : Array UInt8 := mkHashBytes32 0x99 7

private def prunedMask1Cell : Cell := mkPrunedMask1Cell prunedHashA 17
private def prunedMask7Cell : Cell := mkPrunedMask7Cell prunedHashA prunedHashB prunedHashC 1 5 9

private def invalidSpecialShort : Cell :=
  { bits := #[]
    refs := #[]
    special := true
    levelMask := 0 }

private def invalidTooManyRefs : Cell :=
  { bits := #[]
    refs := Array.replicate 5 Cell.empty
    special := false
    levelMask := 0 }

private def invalidTooManyBits : Cell :=
  { bits := Array.replicate 1024 false
    refs := #[]
    special := false
    levelMask := 0 }

private def expectedHashInt (c : Cell) (i : Nat) : Except Excno Int := do
  let info ←
    match c.computeLevelInfo? with
    | .ok v => pure v
    | .error _ => throw .cellUnd
  pure (Int.ofNat (bytesToNatBE (info.getHash i)))

private def chashIModel (i : Nat) (stack : Array Value) : Except Excno (Array Value) := do
  if stack.size = 0 then
    throw .stkUnd
  let top := stack.back!
  let below := stack.extract 0 (stack.size - 1)
  match top with
  | .cell c =>
      let h ← expectedHashInt c i
      pure (below.push (intV h))
  | _ =>
      throw .typeChk

private def expectDirectMatchesModel (label : String) (i : Nat) (stack : Array Value) : IO Unit := do
  match chashIModel i stack with
  | .ok expected =>
      expectOkStack label (runChashIDirect i stack) expected
  | .error e =>
      expectErr label (runChashIDirect i stack) e

private def chashISetGasExactByI : Array Int :=
  #[
    computeExactGasBudget (chashIInstr 0),
    computeExactGasBudget (chashIInstr 1),
    computeExactGasBudget (chashIInstr 2),
    computeExactGasBudget (chashIInstr 3)
  ]

private def chashISetGasExactMinusOneByI : Array Int :=
  chashISetGasExactByI.map (fun g => if g > 0 then g - 1 else 0)

private def fuzzCellPool : Array Cell :=
  #[Cell.empty, ordLeaf, ordOneRef, ordTwoRefs, ordDeep, prunedMask1Cell, prunedMask7Cell]

private def fuzzNoisePool : Array Value :=
  #[.null, intV 37, .slice (Slice.ofCell ordLeaf), .builder Builder.empty, .tuple #[]]

private def pickChashIIndex (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 3

private def pickFuzzCell (rng : StdGen) : Cell × StdGen :=
  let (idx, rng') := randNat rng 0 (fuzzCellPool.size - 1)
  (fuzzCellPool[idx]!, rng')

private def pickFuzzNoise (rng : StdGen) : Value × StdGen :=
  let (idx, rng') := randNat rng 0 (fuzzNoisePool.size - 1)
  (fuzzNoisePool[idx]!, rng')

private def genChashIFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  let (i, rng2) := pickChashIIndex rng1
  let (cell, rng3) := pickFuzzCell rng2
  let (case0, rng4) :=
    if shape = 0 then
      (mkChashICase s!"fuzz/ok/direct/i-{i}" i #[.cell cell], rng3)
    else if shape = 1 then
      let (noise, rng') := pickFuzzNoise rng3
      (mkChashICase s!"fuzz/ok/deep1/i-{i}" i #[noise, .cell cell], rng')
    else if shape = 2 then
      let (noise1, rng') := pickFuzzNoise rng3
      let (noise2, rng'') := pickFuzzNoise rng'
      (mkChashICase s!"fuzz/ok/deep2/i-{i}" i #[noise1, noise2, .cell cell], rng'')
    else if shape = 3 then
      (mkChashICase s!"fuzz/underflow/i-{i}" i #[], rng3)
    else if shape = 4 then
      (mkChashICase s!"fuzz/type/null/i-{i}" i #[.null], rng3)
    else if shape = 5 then
      (mkChashICase s!"fuzz/type/int/i-{i}" i #[intV (-9)], rng3)
    else if shape = 6 then
      (mkChashICase s!"fuzz/type/slice/i-{i}" i #[.slice (Slice.ofCell ordLeaf)], rng3)
    else if shape = 7 then
      (mkChashICase s!"fuzz/type/builder/i-{i}" i #[.builder Builder.empty], rng3)
    else if shape = 8 then
      (mkChashICase s!"fuzz/type/order/top-not-cell/i-{i}" i #[.cell ordLeaf, .null], rng3)
    else if shape = 9 then
      (mkChashICase s!"fuzz/ok/pruned-mask1/i-{i}" i #[.cell prunedMask1Cell], rng3)
    else if shape = 10 then
      (mkChashICase s!"fuzz/ok/pruned-mask7/i-{i}" i #[.cell prunedMask7Cell], rng3)
    else if shape = 11 then
      let gas := chashISetGasExactByI[i]!
      (mkChashICase s!"fuzz/gas/exact/i-{i}" i #[.cell cell]
        #[.pushInt (.num gas), .tonEnvOp .setGasLimit, chashIInstr i], rng3)
    else if shape = 12 then
      let gas := chashISetGasExactMinusOneByI[i]!
      (mkChashICase s!"fuzz/gas/exact-minus-one/i-{i}" i #[.cell cell]
        #[.pushInt (.num gas), .tonEnvOp .setGasLimit, chashIInstr i], rng3)
    else if shape = 13 then
      (mkChashICase s!"fuzz/ok/empty/i-{i}" i #[.cell Cell.empty], rng3)
    else
      (mkChashICase s!"fuzz/ok/deep-fixed/i-{i}" i #[.null, intV 11, .cell ordDeep], rng3)
  let (tag, rng5) := randNat rng4 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

private def oracleSuccessCases : Array OracleCase :=
  #[
    mkChashICase "ok/i0-empty-cell" 0 #[.cell Cell.empty],
    mkChashICase "ok/i3-ordinary-leaf" 3 #[.cell ordLeaf],
    mkChashICase "ok/i0-ordinary-one-ref" 0 #[.cell ordOneRef],
    mkChashICase "ok/i2-ordinary-two-refs" 2 #[.cell ordTwoRefs],
    mkChashICase "ok/i0-ordinary-deep" 0 #[.cell ordDeep],
    mkChashICase "ok/i3-ordinary-deep" 3 #[.cell ordDeep],

    mkChashICase "ok/i0-pruned-mask1" 0 #[.cell prunedMask1Cell],
    mkChashICase "ok/i1-pruned-mask1" 1 #[.cell prunedMask1Cell],
    mkChashICase "ok/i2-pruned-mask1-clamped" 2 #[.cell prunedMask1Cell],
    mkChashICase "ok/i3-pruned-mask1-clamped" 3 #[.cell prunedMask1Cell],

    mkChashICase "ok/i0-pruned-mask7" 0 #[.cell prunedMask7Cell],
    mkChashICase "ok/i1-pruned-mask7" 1 #[.cell prunedMask7Cell],
    mkChashICase "ok/i2-pruned-mask7" 2 #[.cell prunedMask7Cell],
    mkChashICase "ok/i3-pruned-mask7" 3 #[.cell prunedMask7Cell],

    mkChashICase "ok/deep-stack-pruned-mask7-i2" 2 #[.null, intV 123, .cell prunedMask7Cell]
  ]

private def oracleErrorCases : Array OracleCase :=
  #[
    mkChashICase "underflow/empty-i0" 0 #[],
    mkChashICase "underflow/empty-i3" 3 #[],
    mkChashICase "type/top-null" 0 #[.null],
    mkChashICase "type/top-int" 1 #[intV (-5)],
    mkChashICase "type/top-slice" 2 #[.slice (Slice.ofCell ordLeaf)],
    mkChashICase "type/top-builder" 3 #[.builder Builder.empty],
    mkChashICase "error-order/top-not-cell-over-cell" 0 #[.cell ordLeaf, .null]
  ]

private def oracleGasCases : Array OracleCase :=
  #[
    mkChashICase "gas/exact-cost-succeeds-i0" 0 #[.cell ordDeep]
      #[.pushInt (.num chashISetGasExactByI[0]!), .tonEnvOp .setGasLimit, chashIInstr 0],
    mkChashICase "gas/exact-minus-one-out-of-gas-i0" 0 #[.cell ordDeep]
      #[.pushInt (.num chashISetGasExactMinusOneByI[0]!), .tonEnvOp .setGasLimit, chashIInstr 0]
  ]

def suite : InstrSuite where
  id := { name := "CHASHI" }
  unit := #[
    { name := "unit/direct/success-index-selection-and-clamp"
      run := do
        let checks : Array (Nat × Array Value) :=
          #[
            (0, #[.cell Cell.empty]),
            (1, #[.cell ordLeaf]),
            (2, #[.cell ordOneRef]),
            (3, #[.cell ordTwoRefs]),
            (0, #[.cell prunedMask1Cell]),
            (1, #[.cell prunedMask1Cell]),
            (2, #[.cell prunedMask7Cell]),
            (3, #[.cell prunedMask7Cell]),
            (2, #[.null, intV 77, .cell ordDeep])
          ]
        for (i, stack) in checks do
          expectDirectMatchesModel s!"model/i-{i}" i stack

        let r1 := runChashIDirect 1 #[.cell prunedMask1Cell]
        let r2 := runChashIDirect 2 #[.cell prunedMask1Cell]
        let r3 := runChashIDirect 3 #[.cell prunedMask1Cell]
        match r1, r2, r3 with
        | .ok s1, .ok s2, .ok s3 =>
            if s1 == s2 && s2 == s3 then
              pure ()
            else
              throw (IO.userError s!"clamp/mask1: expected i=1,2,3 same, got {reprStr s1}, {reprStr s2}, {reprStr s3}")
        | _, _, _ =>
            throw (IO.userError s!"clamp/mask1: expected success, got {reprStr r1}, {reprStr r2}, {reprStr r3}") }
    ,
    { name := "unit/direct/underflow-type-cellund-and-order"
      run := do
        expectErr "underflow/empty" (runChashIDirect 0 #[]) .stkUnd
        expectErr "type/top-null" (runChashIDirect 0 #[.null]) .typeChk
        expectErr "type/top-int" (runChashIDirect 1 #[intV 1]) .typeChk
        expectErr "type/top-slice" (runChashIDirect 2 #[.slice (Slice.ofCell ordLeaf)]) .typeChk
        expectErr "type/top-builder" (runChashIDirect 3 #[.builder Builder.empty]) .typeChk
        expectErr "type/order-top-not-cell-over-cell"
          (runChashIDirect 0 #[.cell ordLeaf, .null]) .typeChk

        expectErr "cellund/invalid-special-short"
          (runChashIDirect 0 #[.cell invalidSpecialShort]) .cellUnd
        expectErr "cellund/invalid-too-many-refs"
          (runChashIDirect 0 #[.cell invalidTooManyRefs]) .cellUnd
        expectErr "cellund/invalid-too-many-bits"
          (runChashIDirect 0 #[.cell invalidTooManyBits]) .cellUnd }
    ,
    { name := "unit/opcode/decode-boundaries-and-assembler-range"
      run := do
        let program : Array Instr :=
          #[chashIInstr 0, chashIInstr 1, chashIInstr 2, chashIInstr 3, .cellOp (.cdepthI 0), .cellOp .chashIX, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/chashi-program failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/chashi-0" s0 (chashIInstr 0) 16
        let s2 ← expectDecodeStep "decode/chashi-1" s1 (chashIInstr 1) 16
        let s3 ← expectDecodeStep "decode/chashi-2" s2 (chashIInstr 2) 16
        let s4 ← expectDecodeStep "decode/chashi-3" s3 (chashIInstr 3) 16
        let s5 ← expectDecodeStep "decode/cdepthi-0-neighbor" s4 (.cellOp (.cdepthI 0)) 16
        let s6 ← expectDecodeStep "decode/chashix-neighbor" s5 (.cellOp .chashIX) 16
        let s7 ← expectDecodeStep "decode/tail-add" s6 .add 8
        if s7.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s7.bitsRemaining} bits remaining")

        for i in [0:4] do
          let single ←
            match assembleCp0 [chashIInstr i] with
            | .ok cell => pure cell
            | .error e => throw (IO.userError s!"assemble/chashi-{i} failed: {e}")
          let expected := natToBits (chashIWord i) 16
          if single.bits = expected then
            pure ()
          else
            throw (IO.userError
              s!"assemble/chashi-{i}: expected opcode {chashIWord i}, got bits {single.bits}")

        match assembleCp0 [chashIInstr 4] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/chashi-4: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/chashi-4: expected rangeChk, got success")

        match assembleCp0 [chashIInstr 99] with
        | .error .rangeChk => pure ()
        | .error e => throw (IO.userError s!"assemble/chashi-99: expected rangeChk, got {e}")
        | .ok _ => throw (IO.userError "assemble/chashi-99: expected rangeChk, got success")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBoundary : Cell :=
          Cell.mkOrdinary
            (natToBits 0xd767 16 ++ natToBits 0xd768 16 ++ natToBits 0xd76b 16 ++
             natToBits 0xd76c 16 ++ natToBits 0xd770 16 ++ addCell.bits) #[]
        let r0 := Slice.ofCell rawBoundary
        let r1 ← expectDecodeStep "decode/raw-clevelmask-left" r0 (.cellOp .clevelMask) 16
        let r2 ← expectDecodeStep "decode/raw-chashi-0" r1 (chashIInstr 0) 16
        let r3 ← expectDecodeStep "decode/raw-chashi-3" r2 (chashIInstr 3) 16
        let r4 ← expectDecodeStep "decode/raw-cdepthi-0-right" r3 (.cellOp (.cdepthI 0)) 16
        let r5 ← expectDecodeStep "decode/raw-chashix-right" r4 (.cellOp .chashIX) 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-chashi-falls-through"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runChashIDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-cdepthi"
          (runChashIDispatchFallback (.cellOp (.cdepthI 1)) #[intV (-3)])
          #[intV (-3), intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-clevel"
          (runChashIDispatchFallback (.cellOp .clevel) #[.cell ordLeaf])
          #[.cell ordLeaf, intV dispatchSentinel] }
    ,
    { name := "unit/direct/unreachable-immediates-above-3-clamp-not-rangechk"
      run := do
        expectDirectMatchesModel "clamp/pruned7-i4" 4 #[.cell prunedMask7Cell]
        expectDirectMatchesModel "clamp/pruned7-i99" 99 #[.cell prunedMask7Cell]
        expectDirectMatchesModel "clamp/ordinary-i5" 5 #[.cell ordDeep]

        let r3 := runChashIDirect 3 #[.cell prunedMask7Cell]
        let r99 := runChashIDirect 99 #[.cell prunedMask7Cell]
        match r3, r99 with
        | .ok s3, .ok s99 =>
            if s3 == s99 then
              pure ()
            else
              throw (IO.userError s!"clamp/pruned7: expected i=3 and i=99 same, got {reprStr s3} vs {reprStr s99}")
        | _, _ =>
            throw (IO.userError s!"clamp/pruned7: expected success, got {reprStr r3} and {reprStr r99}")

        match runChashIDirect 42 #[.cell ordLeaf] with
        | .error .rangeChk =>
            throw (IO.userError "direct/chashi-42: unexpected rangeChk at runtime")
        | _ => pure () }
  ]
  oracle := oracleSuccessCases ++ oracleErrorCases ++ oracleGasCases
  fuzz := #[
    { seed := 2026021104
      count := 320
      gen := genChashIFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CHASHI
