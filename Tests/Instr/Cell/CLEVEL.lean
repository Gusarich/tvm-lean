import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.CLEVEL

/-
CLEVEL branch mapping (Lean + TVM reference):
- dispatch: only `.cellOp .clevel` is handled; non-target ops must fall through to `next`;
- stack checks: `popCell` yields `stkUnd` / `typeChk` / success;
- success: pushes `LevelMask.getLevel c.levelMask` as a small int;
- opcode/decode: canonical word `0xd766` with 16-bit decode boundary among nearby `0xd76x` cell ops.
-/

private def clevelId : InstrId := { name := "CLEVEL" }

private def clevelInstr : Instr := .cellOp .clevel

private def clevelWord : Nat := 0xd766

private def dispatchSentinel : Int := 766

private def execInstrCellOpClevelOnly (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op => execCellOpClevel op next
  | _ => next

private def mkClevelCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[clevelInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := clevelId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkClevelProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := clevelId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runClevelDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrCellOpClevelOnly clevelInstr stack

private def runClevelDispatchFallback (instr : Instr) (stack : Array Value) :
    Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrCellOpClevelOnly instr (VM.push (intV dispatchSentinel)) stack

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

private def clevelSetGasExact : Int :=
  computeExactGasBudget clevelInstr

private def clevelSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne clevelInstr

private def bitsFromBytes (bytes : Array UInt8) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

private def mkLibraryCell (hashSeed : Nat := 0) : Cell :=
  { bits := natToBits 2 8 ++ natToBits hashSeed 256
    refs := #[]
    special := true
    levelMask := 0 }

private def mkPrunedCell (mask : Nat) (seed : Nat := 0) : Cell :=
  let hashCount : Nat := LevelMask.getHashI mask
  let hashBytes : Array UInt8 :=
    Array.ofFn (n := hashCount * 32) fun i =>
      UInt8.ofNat ((seed + (i.1 * 37) + mask * 11) % 256)
  let depthBytes : Array UInt8 :=
    Array.ofFn (n := hashCount * 2) fun i =>
      if i.1 % 2 = 0 then
        UInt8.ofNat (((seed / 7) + mask + i.1) % 4)
      else
        UInt8.ofNat ((seed + i.1 + mask * 3) % 251)
  let payload : Array UInt8 := #[UInt8.ofNat 1, UInt8.ofNat mask] ++ hashBytes ++ depthBytes
  { bits := bitsFromBytes payload
    refs := #[]
    special := true
    levelMask := mask }

private def cOrd0 : Cell :=
  Cell.empty

private def cOrdBits : Cell :=
  Cell.ofUInt 9 0x1A5

private def cPruned1 : Cell :=
  mkPrunedCell 1 17

private def cPruned2 : Cell :=
  mkPrunedCell 2 29

private def cPruned3 : Cell :=
  mkPrunedCell 3 41

private def cPruned4 : Cell :=
  mkPrunedCell 4 53

private def cPruned5 : Cell :=
  mkPrunedCell 5 67

private def cPruned7 : Cell :=
  mkPrunedCell 7 89

private def cLibrary0 : Cell :=
  mkLibraryCell 0xA5

private def cOrdRefMask1 : Cell :=
  Cell.mkOrdinary (natToBits 0b1011 4) #[cPruned1]

private def cOrdRefMask2 : Cell :=
  Cell.mkOrdinary (natToBits 0x2D 6) #[cPruned2]

private def cOrdRefMask4 : Cell :=
  Cell.mkOrdinary (natToBits 0x35 6) #[cPruned4]

private def cOrdRefs12 : Cell :=
  Cell.mkOrdinary (natToBits 0x5A 7) #[cPruned1, cPruned2]

private def cOrdRefs24 : Cell :=
  Cell.mkOrdinary (natToBits 0x7F 7) #[cPruned2, cPruned4]

private def cOrdRefsMixed7 : Cell :=
  Cell.mkOrdinary (natToBits 0x41 7) #[cPruned5, cPruned2]

private def cOrdNested7 : Cell :=
  Cell.mkOrdinary (natToBits 0x123 10) #[cOrdRefs24, cPruned1]

private def cWeirdMask9 : Cell :=
  -- Direct handler path is mask-driven and does not clamp to 3-bit masks.
  { bits := #[]
    refs := #[]
    special := true
    levelMask := 9 }

private def expectedClevelOut (below : Array Value) (c : Cell) : Array Value :=
  below ++ #[intV (Int.ofNat (LevelMask.getLevel c.levelMask))]

def suite : InstrSuite where
  id := clevelId
  unit := #[
    -- Branch: success path computes `getLevel(levelMask)` and preserves lower stack.
    { name := "unit/direct/success-level-computation-and-stack-contract"
      run := do
        let checks : Array (String × Cell) :=
          #[
            ("ordinary-empty", cOrd0),
            ("ordinary-bits-only", cOrdBits),
            ("special-pruned-mask1", cPruned1),
            ("special-pruned-mask2", cPruned2),
            ("special-pruned-mask4", cPruned4),
            ("special-pruned-mask7", cPruned7),
            ("ordinary-ref-mask1", cOrdRefMask1),
            ("ordinary-ref-mask2", cOrdRefMask2),
            ("ordinary-ref-mask4", cOrdRefMask4),
            ("ordinary-refs12", cOrdRefs12),
            ("ordinary-refs24", cOrdRefs24),
            ("ordinary-refs-mixed7", cOrdRefsMixed7),
            ("ordinary-nested-mask7", cOrdNested7),
            ("special-library-mask0", cLibrary0),
            ("weird-mask9-direct", cWeirdMask9)
          ]
        for (label, c) in checks do
          expectOkStack s!"ok/{label}"
            (runClevelDirect #[.cell c])
            (expectedClevelOut #[] c)

        let below : Array Value := #[.null, intV (-8), .cell cOrd0]
        expectOkStack "ok/deep-stack-preserved"
          (runClevelDirect (below ++ #[.cell cOrdRefs24]))
          (expectedClevelOut below cOrdRefs24) }
    ,
    -- Branch: only `popCell` failures are possible in the handler.
    { name := "unit/direct/underflow-and-type-checks"
      run := do
        expectErr "underflow/empty"
          (runClevelDirect #[]) .stkUnd

        expectErr "type/top-null"
          (runClevelDirect #[.null]) .typeChk
        expectErr "type/top-int"
          (runClevelDirect #[intV 5]) .typeChk
        expectErr "type/top-slice"
          (runClevelDirect #[.slice (Slice.ofCell cOrd0)]) .typeChk
        expectErr "type/top-builder"
          (runClevelDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple"
          (runClevelDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont"
          (runClevelDirect #[.cont (.quit 0)]) .typeChk

        expectErr "type/order-top-null-over-valid-cell"
          (runClevelDirect #[.cell cPruned7, .null]) .typeChk }
    ,
    -- Branch invariant: CLEVEL has no immediate-range or cell-shape rejection branches.
    { name := "unit/direct/rangechk-unreachable-for-clevel"
      run := do
        let probes : Array (String × Except Excno (Array Value)) :=
          #[
            ("ok/ordinary", runClevelDirect #[.cell cOrd0]),
            ("ok/special", runClevelDirect #[.cell cPruned3]),
            ("underflow", runClevelDirect #[]),
            ("type", runClevelDirect #[.null])
          ]
        for (label, res) in probes do
          match res with
          | .error .rangeChk =>
              throw (IO.userError s!"{label}: unexpected rangeChk for CLEVEL")
          | _ => pure () }
    ,
    -- Branch: canonical encoding + decode boundaries around the 0xd76x cluster.
    { name := "unit/opcode/decode-and-assembler-boundaries"
      run := do
        let assembled ←
          match assembleCp0 [clevelInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/clevel failed: {e}")
        if assembled.bits = natToBits clevelWord 16 then
          pure ()
        else
          throw (IO.userError s!"assemble/clevel: expected 0xd766, got {reprStr assembled.bits}")

        let seq : Array Instr :=
          #[.cdepth, clevelInstr, .cellOp .clevelMask, .cellOp (.chashI 0), .add]
        let code ←
          match assembleCp0 seq.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble/sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/cdepth-neighbor" s0 .cdepth 16
        let s2 ← expectDecodeStep "decode/clevel" s1 clevelInstr 16
        let s3 ← expectDecodeStep "decode/clevelmask-neighbor" s2 (.cellOp .clevelMask) 16
        let s4 ← expectDecodeStep "decode/chashi0-neighbor" s3 (.cellOp (.chashI 0)) 16
        let s5 ← expectDecodeStep "decode/tail-add" s4 .add 8
        if s5.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s5.bitsRemaining} bits remaining")

        expectDecodeErr "decode/hole-0xd763-invalid"
          (mkSliceFromBits (natToBits 0xd763 16)) .invOpcode

        expectDecodeErr "decode/truncated-prefix-8bits-d7"
          (mkSliceFromBits (natToBits 0xd7 8)) .invOpcode

        let raw := mkSliceFromBits (natToBits clevelWord 16 ++ natToBits 0xd767 16)
        let r1 ← expectDecodeStep "decode/raw-clevel" raw clevelInstr 16
        let r2 ← expectDecodeStep "decode/raw-tail-clevelmask" r1 (.cellOp .clevelMask) 16
        if r2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted slice, got {r2.bitsRemaining} bits remaining") }
    ,
    -- Branch: next-handler pass-through for non-target instructions.
    { name := "unit/dispatch/fallback-and-target-match"
      run := do
        expectOkStack "dispatch/handled-clevel"
          (runClevelDispatchFallback clevelInstr #[.cell cPruned4])
          (expectedClevelOut #[] cPruned4)

        expectOkStack "dispatch/non-cellop-add"
          (runClevelDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-clevelmask"
          (runClevelDispatchFallback (.cellOp .clevelMask) #[intV 3])
          #[intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/other-cellop-sdepth"
          (runClevelDispatchFallback (.cellOp .sdepth) #[.cell cOrd0])
          #[.cell cOrd0, intV dispatchSentinel] }
    ,
    -- Branch: `getLevel` monotonic edge expectations on representative masks.
    { name := "unit/direct/getlevel-boundary-sanity"
      run := do
        let masks : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        for m in masks do
          let c : Cell := { bits := #[], refs := #[], special := true, levelMask := m }
          expectOkStack s!"mask-{m}"
            (runClevelDirect #[.cell c])
            #[intV (Int.ofNat (LevelMask.getLevel m))] }
  ]
  oracle := #[
    mkClevelCase "ok/ordinary-empty" #[.cell cOrd0],
    mkClevelCase "ok/ordinary-bits-only" #[.cell cOrdBits],
    mkClevelCase "ok/special-library-mask0" #[.cell cLibrary0],
    mkClevelCase "ok/special-pruned-mask1" #[.cell cPruned1],
    mkClevelCase "ok/special-pruned-mask2" #[.cell cPruned2],
    mkClevelCase "ok/special-pruned-mask3" #[.cell cPruned3],
    mkClevelCase "ok/special-pruned-mask4" #[.cell cPruned4],
    mkClevelCase "ok/special-pruned-mask7" #[.cell cPruned7],
    mkClevelCase "ok/ordinary-ref-mask1" #[.cell cOrdRefMask1],
    mkClevelCase "ok/ordinary-ref-mask2" #[.cell cOrdRefMask2],
    mkClevelCase "ok/ordinary-ref-mask4" #[.cell cOrdRefMask4],
    mkClevelCase "ok/ordinary-refs12" #[.cell cOrdRefs12],
    mkClevelCase "ok/ordinary-refs24" #[.cell cOrdRefs24],
    mkClevelCase "ok/ordinary-refs-mixed7" #[.cell cOrdRefsMixed7],
    mkClevelCase "ok/ordinary-nested-mask7" #[.cell cOrdNested7],
    mkClevelCase "ok/deep-stack-null-below" #[.null, .cell cOrdRefs24],
    mkClevelCase "ok/deep-stack-two-below" #[intV (-11), .cell cOrd0, .cell cPruned7],

    mkClevelCase "underflow/empty" #[],
    mkClevelCase "type/top-null" #[.null],
    mkClevelCase "type/top-int" #[intV 1],
    mkClevelCase "type/top-builder" #[.builder Builder.empty],
    mkClevelCase "type/top-slice" #[.slice (Slice.ofCell cOrd0)],
    mkClevelCase "type/top-tuple-empty" #[.tuple #[]],
    mkClevelCase "type/top-cont-quit0" #[.cont (.quit 0)],
    mkClevelCase "type/order-top-null-over-valid-cell" #[.cell cPruned7, .null],

    mkClevelProgramCase "gas/exact-cost-succeeds"
      #[.cell cPruned4]
      #[.pushInt (.num clevelSetGasExact), .tonEnvOp .setGasLimit, clevelInstr],
    mkClevelProgramCase "gas/exact-minus-one-out-of-gas"
      #[.cell cPruned4]
      #[.pushInt (.num clevelSetGasExactMinusOne), .tonEnvOp .setGasLimit, clevelInstr]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.CLEVEL
