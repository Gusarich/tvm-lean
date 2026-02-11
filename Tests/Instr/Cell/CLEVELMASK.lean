import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CLEVELMASK

/-
CLEVELMASK branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/CellOp/ClevelMask.lean` (`.clevelMask`)
  - `TvmLean/Semantics/Exec/CellOp.lean` (cell-op dispatch chain)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`CLEVELMASK` encode: `0xd767`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xd765..0xd771` neighborhood decode)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (`exec_cell_level_mask`, opcode registration `0xd767`).

Branch map covered by this suite:
- dispatch guard for `.cellOp .clevelMask` vs fallback to `next`;
- single pop via `VM.popCell`: underflow (`stkUnd`) and strict top-type (`typeChk`);
- success path pushes `cell.levelMask` exactly (including non-zero / non-canonical masks);
- opcode/decode boundaries around `0xd767` with adjacent `CDEPTH/CLEVEL/CHASHI/CDEPTHI`.
-/

private def clevelMaskId : InstrId := { name := "CLEVELMASK" }

private def clevelMaskInstr : Instr := .cellOp .clevelMask
private def clevelInstr : Instr := .cellOp .clevel
private def cdepthInstr : Instr := .cdepth
private def chashI0Instr : Instr := .cellOp (.chashI 0)
private def chashI3Instr : Instr := .cellOp (.chashI 3)
private def cdepthI0Instr : Instr := .cellOp (.cdepthI 0)
private def cdepthI3Instr : Instr := .cellOp (.cdepthI 3)
private def chashIXInstr : Instr := .cellOp .chashIX
private def cdepthIXInstr : Instr := .cellOp .cdepthIX

private def cdepthWord : Nat := 0xd765
private def clevelWord : Nat := 0xd766
private def clevelMaskWord : Nat := 0xd767
private def chashI0Word : Nat := 0xd768
private def chashI3Word : Nat := 0xd76b

private def dispatchSentinel : Int := 1767

private def execInstrCellOpClevelMaskOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpClevelMask op next
  | _ => next

private def mkClevelMaskCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[clevelMaskInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := clevelMaskId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runClevelMaskDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpClevelMaskOnly clevelMaskInstr stack

private def runClevelMaskDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpClevelMaskOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def stripeBits (count : Nat) (phase : Nat := 0) : BitString :=
  Array.ofFn (n := count) fun i => ((i.1 + phase) % 2 = 1)

private def refLeafB : Cell := Cell.mkOrdinary (natToBits 13 4) #[]

private def cellOrdinaryEmpty : Cell := Cell.empty
private def cellOrdinaryBits : Cell := Cell.mkOrdinary (stripeBits 37 1) #[]
private def cellOrdinaryRefs : Cell := Cell.mkOrdinary (stripeBits 11 0) #[refLeafA, refLeafB]

private def mkPrunedBranchBits (mask : Nat) : BitString :=
  let hashCnt := LevelMask.getHashI mask
  let totalBytes : Nat := 2 + hashCnt * (32 + 2)
  natToBits 1 8 ++ natToBits mask 8 ++ Array.replicate ((totalBytes - 2) * 8) false

private def mkPrunedBranchCell (mask : Nat) : Cell :=
  { bits := mkPrunedBranchBits mask
    refs := #[]
    special := true
    levelMask := mask }

private def cellPrunedMask1 : Cell := mkPrunedBranchCell 1
private def cellPrunedMask3 : Cell := mkPrunedBranchCell 3
private def cellPrunedMask7 : Cell := mkPrunedBranchCell 7

private def cellOrdinaryWithPrunedRef1 : Cell :=
  Cell.mkOrdinary (stripeBits 7 0) #[cellPrunedMask1]

private def cellOrdinaryWithPrunedRefs37 : Cell :=
  Cell.mkOrdinary (stripeBits 9 1) #[cellPrunedMask3, cellPrunedMask7]

private def cellManualMask13 : Cell :=
  { bits := stripeBits 10 1
    refs := #[]
    special := false
    levelMask := 13 }

private def expectWellFormed (label : String) (c : Cell) : IO Unit := do
  match c.computeLevelInfo? with
  | .ok info =>
      if info.levelMask = c.levelMask then
        pure ()
      else
        throw (IO.userError s!"{label}: computed levelMask={info.levelMask} differs from stored={c.levelMask}")
  | .error e =>
      throw (IO.userError s!"{label}: expected well-formed cell, got error: {e}")

private def programNewcEndcClevelMask : Array Instr :=
  #[.newc, .endc, clevelMaskInstr]

private def programNewcStu8EndcClevelMask : Array Instr :=
  #[.newc, .pushInt (.num 173), .xchg0 1, .stu 8, .endc, clevelMaskInstr]

private def programNewcStu256EndcClevelMask : Array Instr :=
  #[.newc, .pushInt (.num 0), .xchg0 1, .stu 256, .endc, clevelMaskInstr]

private def programPushNullNewcStu8EndcClevelMask : Array Instr :=
  #[.pushNull] ++ programNewcStu8EndcClevelMask

private def clevelMaskSetGasExact : Int :=
  computeExactGasBudget clevelMaskInstr

private def clevelMaskSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne clevelMaskInstr

private def oracleSuccessCellPool : Array (String × Cell) :=
  #[
    ("ord-empty-mask0", cellOrdinaryEmpty),
    ("ord-bits-mask0", cellOrdinaryBits),
    ("ord-refs-mask0", cellOrdinaryRefs),
    ("pruned-mask1", cellPrunedMask1),
    ("pruned-mask3", cellPrunedMask3),
    ("pruned-mask7", cellPrunedMask7),
    ("ord-pruned-ref-mask1", cellOrdinaryWithPrunedRef1),
    ("ord-pruned-refs-mask7", cellOrdinaryWithPrunedRefs37)
  ]

private def pickOracleSuccessCell (rng : StdGen) : (String × Cell) × StdGen :=
  let (idx, rng') := randNat rng 0 (oracleSuccessCellPool.size - 1)
  (oracleSuccessCellPool[idx]!, rng')

private def oracleNoisePool : Array (String × Value) :=
  #[
    ("null", .null),
    ("int", intV 41),
    ("cell", .cell cellOrdinaryBits),
    ("slice", .slice (Slice.ofCell cellOrdinaryRefs)),
    ("builder", .builder Builder.empty),
    ("tuple", .tuple #[]),
    ("cont", .cont (.quit 0))
  ]

private def pickOracleNoise (rng : StdGen) : (String × Value) × StdGen :=
  let (idx, rng') := randNat rng 0 (oracleNoisePool.size - 1)
  (oracleNoisePool[idx]!, rng')

private def oracleBadTopPool : Array (String × Value) :=
  #[
    ("null", .null),
    ("int", intV (-7)),
    ("slice", .slice (Slice.ofCell cellOrdinaryBits)),
    ("builder", .builder Builder.empty),
    ("tuple", .tuple #[]),
    ("cont", .cont (.quit 0))
  ]

private def pickOracleBadTop (rng : StdGen) : (String × Value) × StdGen :=
  let (idx, rng') := randNat rng 0 (oracleBadTopPool.size - 1)
  (oracleBadTopPool[idx]!, rng')

private def genClevelMaskFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let ((tag, c), rng2) := pickOracleSuccessCell rng1
      (mkClevelMaskCase s!"fuzz/ok/direct/{tag}" #[.cell c], rng2)
    else if shape = 1 then
      let ((cellTag, c), rng2) := pickOracleSuccessCell rng1
      let ((noiseTag, noise), rng3) := pickOracleNoise rng2
      (mkClevelMaskCase s!"fuzz/ok/deep1/{noiseTag}/{cellTag}" #[noise, .cell c], rng3)
    else if shape = 2 then
      let ((cellTag, c), rng2) := pickOracleSuccessCell rng1
      let ((noiseTagA, noiseA), rng3) := pickOracleNoise rng2
      let ((noiseTagB, noiseB), rng4) := pickOracleNoise rng3
      (mkClevelMaskCase s!"fuzz/ok/deep2/{noiseTagA}-{noiseTagB}/{cellTag}"
        #[noiseA, noiseB, .cell c], rng4)
    else if shape = 3 then
      (mkClevelMaskCase "fuzz/underflow/empty" #[], rng1)
    else if shape = 4 then
      let ((badTag, bad), rng2) := pickOracleBadTop rng1
      (mkClevelMaskCase s!"fuzz/type/top-{badTag}" #[bad], rng2)
    else if shape = 5 then
      let ((badTag, bad), rng2) := pickOracleBadTop rng1
      (mkClevelMaskCase s!"fuzz/type/order-top-{badTag}" #[.cell cellPrunedMask3, bad], rng2)
    else if shape = 6 then
      (mkClevelMaskCase "fuzz/ok/program/newc-endc" #[] programNewcEndcClevelMask, rng1)
    else if shape = 7 then
      (mkClevelMaskCase "fuzz/ok/program/newc-stu8-endc" #[] programNewcStu8EndcClevelMask, rng1)
    else if shape = 8 then
      (mkClevelMaskCase "fuzz/ok/program/newc-stu256-endc" #[] programNewcStu256EndcClevelMask, rng1)
    else if shape = 9 then
      (mkClevelMaskCase "fuzz/ok/program/noise-newc-stu8-endc" #[] programPushNullNewcStu8EndcClevelMask, rng1)
    else if shape = 10 then
      let ((tag, c), rng2) := pickOracleSuccessCell rng1
      (mkClevelMaskCase s!"fuzz/gas/exact/{tag}" #[.cell c]
        #[.pushInt (.num clevelMaskSetGasExact), .tonEnvOp .setGasLimit, clevelMaskInstr], rng2)
    else if shape = 11 then
      let ((tag, c), rng2) := pickOracleSuccessCell rng1
      (mkClevelMaskCase s!"fuzz/gas/exact-minus-one/{tag}" #[.cell c]
        #[.pushInt (.num clevelMaskSetGasExactMinusOne), .tonEnvOp .setGasLimit, clevelMaskInstr], rng2)
    else if shape = 12 then
      (mkClevelMaskCase "fuzz/ok/direct/pruned7" #[.cell cellPrunedMask7], rng1)
    else if shape = 13 then
      (mkClevelMaskCase "fuzz/ok/direct/ord-pruned-ref1" #[.cell cellOrdinaryWithPrunedRef1], rng1)
    else if shape = 14 then
      let ((noiseTag, noise), rng2) := pickOracleNoise rng1
      (mkClevelMaskCase s!"fuzz/ok/preserve-below/{noiseTag}" #[noise, .cell cellPrunedMask1], rng2)
    else
      let ((badTag, bad), rng2) := pickOracleBadTop rng1
      let ((noiseTag, noise), rng3) := pickOracleNoise rng2
      (mkClevelMaskCase s!"fuzz/type/deep/{noiseTag}/top-{badTag}" #[noise, .cell cellPrunedMask1, bad], rng3)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := { name := "CLEVELMASK" }
  unit := #[
    { name := "unit/fixtures/pruned-cells-are-well-formed"
      run := do
        expectWellFormed "fixture/pruned-mask1" cellPrunedMask1
        expectWellFormed "fixture/pruned-mask3" cellPrunedMask3
        expectWellFormed "fixture/pruned-mask7" cellPrunedMask7
        expectWellFormed "fixture/ordinary-with-pruned-ref1" cellOrdinaryWithPrunedRef1
        expectWellFormed "fixture/ordinary-with-pruned-refs37" cellOrdinaryWithPrunedRefs37 }
    ,
    { name := "unit/direct/success-levelmask-values-and-stack-preservation"
      run := do
        expectOkStack "ok/ordinary-empty-mask0"
          (runClevelMaskDirect #[.cell cellOrdinaryEmpty])
          #[intV 0]
        expectOkStack "ok/ordinary-bits-mask0"
          (runClevelMaskDirect #[.cell cellOrdinaryBits])
          #[intV 0]
        expectOkStack "ok/ordinary-refs-mask0"
          (runClevelMaskDirect #[.cell cellOrdinaryRefs])
          #[intV 0]
        expectOkStack "ok/pruned-mask1"
          (runClevelMaskDirect #[.cell cellPrunedMask1])
          #[intV 1]
        expectOkStack "ok/pruned-mask3"
          (runClevelMaskDirect #[.cell cellPrunedMask3])
          #[intV 3]
        expectOkStack "ok/pruned-mask7"
          (runClevelMaskDirect #[.cell cellPrunedMask7])
          #[intV 7]
        expectOkStack "ok/ordinary-with-pruned-ref-mask1"
          (runClevelMaskDirect #[.cell cellOrdinaryWithPrunedRef1])
          #[intV 1]
        expectOkStack "ok/ordinary-with-pruned-refs-mask7"
          (runClevelMaskDirect #[.cell cellOrdinaryWithPrunedRefs37])
          #[intV 7]
        expectOkStack "ok/manual-noncanonical-mask13-passed-through"
          (runClevelMaskDirect #[.cell cellManualMask13])
          #[intV 13]
        expectOkStack "ok/deep-stack-preserved"
          (runClevelMaskDirect #[.null, intV 44, .cell cellPrunedMask3])
          #[.null, intV 44, intV 3] }
    ,
    { name := "unit/direct/underflow-type-and-top-order"
      run := do
        expectErr "underflow/empty"
          (runClevelMaskDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runClevelMaskDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runClevelMaskDirect #[intV 0]) .typeChk
        expectErr "type/top-slice"
          (runClevelMaskDirect #[.slice (Slice.ofCell cellOrdinaryBits)]) .typeChk
        expectErr "type/top-builder"
          (runClevelMaskDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple-empty"
          (runClevelMaskDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont-quit0"
          (runClevelMaskDirect #[.cont (.quit 0)]) .typeChk

        expectErr "order/top-null-over-cell"
          (runClevelMaskDirect #[.cell cellPrunedMask1, .null]) .typeChk
        expectOkStack "order/top-cell-below-null-preserved"
          (runClevelMaskDirect #[.null, .cell cellPrunedMask1])
          #[.null, intV 1] }
    ,
    { name := "unit/dispatch/fallback-vs-handled"
      run := do
        expectOkStack "dispatch/non-cellop-add"
          (runClevelMaskDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/non-cellop-cdepth"
          (runClevelMaskDispatchFallback cdepthInstr #[.cell cellOrdinaryBits])
          #[.cell cellOrdinaryBits, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-clevel"
          (runClevelMaskDispatchFallback clevelInstr #[.cell cellOrdinaryBits])
          #[.cell cellOrdinaryBits, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-chashi0"
          (runClevelMaskDispatchFallback chashI0Instr #[.cell cellOrdinaryBits])
          #[.cell cellOrdinaryBits, intV dispatchSentinel]
        expectOkStack "dispatch/target-clevelmask-is-handled"
          (runClevelMaskDispatchFallback clevelMaskInstr #[.cell cellPrunedMask3])
          #[intV 3] }
    ,
    { name := "unit/opcode/decode-and-assemble-boundaries"
      run := do
        let clevelMaskCode ←
          match assembleCp0 [clevelMaskInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/clevelmask failed: {e}")
        if clevelMaskCode.bits = natToBits clevelMaskWord 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/clevelmask: expected 0xd767, got bits {clevelMaskCode.bits}")
        if clevelMaskCode.bits.size = 16 then
          pure ()
        else
          throw (IO.userError
            s!"assemble/clevelmask: expected 16 bits, got {clevelMaskCode.bits.size}")
        let s0 := Slice.ofCell clevelMaskCode
        let s1 ← expectDecodeStep "decode/assembled-clevelmask" s0 clevelMaskInstr 16
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/assembled-clevelmask: expected exhausted slice, got {s1.bitsRemaining}")

        let program : Array Instr :=
          #[cdepthInstr, clevelInstr, clevelMaskInstr, chashI0Instr, chashI3Instr,
            cdepthI0Instr, cdepthI3Instr, chashIXInstr, cdepthIXInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/neighborhood failed: {e}")
        let d0 := Slice.ofCell code
        let d1 ← expectDecodeStep "decode/cdepth-left-neighbor" d0 cdepthInstr 16
        let d2 ← expectDecodeStep "decode/clevel-left-neighbor" d1 clevelInstr 16
        let d3 ← expectDecodeStep "decode/clevelmask" d2 clevelMaskInstr 16
        let d4 ← expectDecodeStep "decode/chashi0-right-neighbor" d3 chashI0Instr 16
        let d5 ← expectDecodeStep "decode/chashi3-right-neighbor" d4 chashI3Instr 16
        let d6 ← expectDecodeStep "decode/cdepthi0" d5 cdepthI0Instr 16
        let d7 ← expectDecodeStep "decode/cdepthi3" d6 cdepthI3Instr 16
        let d8 ← expectDecodeStep "decode/chashix" d7 chashIXInstr 16
        let d9 ← expectDecodeStep "decode/cdepthix" d8 cdepthIXInstr 16
        let d10 ← expectDecodeStep "decode/tail-add" d9 .add 8
        if d10.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/neighborhood-end: expected exhausted slice, got {d10.bitsRemaining}")

        let addCell ←
          match assembleCp0 [.add] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/add failed: {e}")
        let rawBits : BitString :=
          natToBits cdepthWord 16
            ++ natToBits clevelWord 16
            ++ natToBits clevelMaskWord 16
            ++ natToBits chashI0Word 16
            ++ natToBits chashI3Word 16
            ++ addCell.bits
        let r0 := mkSliceFromBits rawBits
        let r1 ← expectDecodeStep "decode/raw-cdepth" r0 cdepthInstr 16
        let r2 ← expectDecodeStep "decode/raw-clevel" r1 clevelInstr 16
        let r3 ← expectDecodeStep "decode/raw-clevelmask" r2 clevelMaskInstr 16
        let r4 ← expectDecodeStep "decode/raw-chashi0" r3 chashI0Instr 16
        let r5 ← expectDecodeStep "decode/raw-chashi3" r4 chashI3Instr 16
        let r6 ← expectDecodeStep "decode/raw-tail-add" r5 .add 8
        if r6.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r6.bitsRemaining}")

        let payload := natToBits 0x5a 8
        let w0 := mkSliceFromBits (natToBits clevelMaskWord 16 ++ payload)
        let w1 ← expectDecodeStep "decode/word-clevelmask" w0 clevelMaskInstr 16
        if w1.readBits 8 = payload then
          pure ()
        else
          throw (IO.userError "decode/word-clevelmask: trailing payload mismatch")

        expectDecodeErr "decode/gap-0xd763"
          (mkSliceFromBits (natToBits 0xd763 16)) .invOpcode
        expectDecodeErr "decode/truncated-7b"
          (mkSliceFromBits (natToBits clevelMaskWord 7)) .invOpcode }
  ]
  oracle := #[
    mkClevelMaskCase "ok/direct/ordinary-empty-mask0"
      #[.cell cellOrdinaryEmpty],
    mkClevelMaskCase "ok/direct/ordinary-bits-mask0"
      #[.cell cellOrdinaryBits],
    mkClevelMaskCase "ok/direct/ordinary-refs-mask0"
      #[.cell cellOrdinaryRefs],
    mkClevelMaskCase "ok/direct/pruned-mask1"
      #[.cell cellPrunedMask1],
    mkClevelMaskCase "ok/direct/pruned-mask3"
      #[.cell cellPrunedMask3],
    mkClevelMaskCase "ok/direct/pruned-mask7"
      #[.cell cellPrunedMask7],
    mkClevelMaskCase "ok/direct/ordinary-with-pruned-ref-mask1"
      #[.cell cellOrdinaryWithPrunedRef1],
    mkClevelMaskCase "ok/direct/ordinary-with-pruned-refs-mask7"
      #[.cell cellOrdinaryWithPrunedRefs37],
    mkClevelMaskCase "ok/direct/deep-null-below-pruned3"
      #[.null, .cell cellPrunedMask3],
    mkClevelMaskCase "ok/direct/deep-two-below-pruned1"
      #[intV 5, .cell cellOrdinaryBits, .cell cellPrunedMask1],

    mkClevelMaskCase "ok/program/newc-endc-empty-mask0"
      #[] programNewcEndcClevelMask,
    mkClevelMaskCase "ok/program/newc-stu8-endc-mask0"
      #[] programNewcStu8EndcClevelMask,
    mkClevelMaskCase "ok/program/newc-stu256-endc-mask0"
      #[] programNewcStu256EndcClevelMask,
    mkClevelMaskCase "ok/program/noise-newc-stu8-endc-mask0"
      #[] programPushNullNewcStu8EndcClevelMask,

    mkClevelMaskCase "underflow/empty" #[],
    mkClevelMaskCase "type/top-null" #[.null],
    mkClevelMaskCase "type/top-int" #[intV 0],
    mkClevelMaskCase "type/top-slice" #[.slice (Slice.ofCell cellOrdinaryBits)],
    mkClevelMaskCase "type/top-builder" #[.builder Builder.empty],
    mkClevelMaskCase "type/top-tuple-empty" #[.tuple #[]],
    mkClevelMaskCase "type/top-cont-quit0" #[.cont (.quit 0)],
    mkClevelMaskCase "type/order-top-null-over-cell"
      #[.cell cellPrunedMask1, .null],
    mkClevelMaskCase "type/order-top-int-over-cell"
      #[.cell cellPrunedMask1, intV 99],
    mkClevelMaskCase "type/order-top-slice-over-cell"
      #[.cell cellPrunedMask1, .slice (Slice.ofCell cellOrdinaryRefs)],

    mkClevelMaskCase "ok/direct/deep-cell-noise-pruned7"
      #[.cell cellOrdinaryBits, .cell cellPrunedMask7],
    mkClevelMaskCase "ok/direct/deep-builder-noise-pruned1"
      #[.builder Builder.empty, .cell cellPrunedMask1],
    mkClevelMaskCase "ok/direct/deep-tuple-noise-pruned3"
      #[.tuple #[], .cell cellPrunedMask3],
    mkClevelMaskCase "ok/direct/deep-cont-noise-pruned1"
      #[.cont (.quit 0), .cell cellPrunedMask1],

    mkClevelMaskCase "gas/exact-succeeds"
      #[.cell cellPrunedMask3]
      #[.pushInt (.num clevelMaskSetGasExact), .tonEnvOp .setGasLimit, clevelMaskInstr],
    mkClevelMaskCase "gas/exact-minus-one-out-of-gas"
      #[.cell cellPrunedMask3]
      #[.pushInt (.num clevelMaskSetGasExactMinusOne), .tonEnvOp .setGasLimit, clevelMaskInstr]
  ]
  fuzz := #[
    { seed := 2026021021
      count := 224
      gen := genClevelMaskFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.CLEVELMASK
