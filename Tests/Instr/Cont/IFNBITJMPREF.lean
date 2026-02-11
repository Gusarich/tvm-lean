import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFNBITJMPREF

/-
IFNBITJMPREF branch map (Lean vs C++ `exec_if_bit_jmpref`, negate path):
- decode path: cp0 consumes the inline ref while decoding (`takeRefInv`), matching C++ code-slice
  progression (`advance` + `fetch_ref`) before stack checks;
- opcode dispatch: only `.contExt (.ifnbitjmpref idx code)` handled here, others fall through to `next`;
- stack operand path: C++ uses `pop_int_finite` then re-pushes `x`; Lean must mirror this exactly;
- integer checks: underflow at pop site, non-int => `typeChk`, NaN => `intOv`;
- bit predicate: negate path jumps iff `bit(idx, x) = false` (i.e., `val ^ negate` with `negate = true`);
- taken path: registers cell load and jumps to ordinary continuation built from the ref slice;
- not-taken path: does not register referenced-cell load.

Regression fixed in Lean:
- `IFNBITJMPREF` used `fetch` instead of `popIntFinite`+re-push, which mismatched C++
  stack mutation on pop-site `typeChk` / `intOv`.
-/

private def ifnbitjmprefId : InstrId := { name := "IFNBITJMPREF" }

private def dispatchSentinel : Int := 53117

private def opIfnbitjmprefBase : Nat := 0xe3e0

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def fullSliceB : Slice :=
  Slice.ofCell refCellB

private def bodyEmpty : Cell :=
  Cell.empty

private def bodyPush7 : Cell :=
  Cell.mkOrdinary (natToBits 0x77 8) #[]

private def bodyPush9 : Cell :=
  Cell.mkOrdinary (natToBits 0x79 8) #[]

private def bodySliceEmpty : Slice :=
  Slice.ofCell bodyEmpty

private def bodySlicePush7 : Slice :=
  Slice.ofCell bodyPush7

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def ifnbitjmprefWord (idx : Nat) : Nat :=
  opIfnbitjmprefBase + (idx &&& 0x1f)

private def mkIfnbitjmprefCodeCell
    (idx : Nat)
    (target : Cell)
    (tailBytes : Array Nat := #[]) : Cell :=
  Cell.mkOrdinary (natToBits (ifnbitjmprefWord idx) 16 ++ bytesToBits tailBytes) #[target]

private def ifnbitjmprefInstr (idx : Nat) (code : Slice := bodySliceEmpty) : Instr :=
  .contExt (.ifnbitjmpref idx code)

private def mkStack (below : Array Value) (x : Int) : Array Value :=
  below ++ #[intV x]

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (target : Cell := bodyEmpty)
    (tailBytes : Array Nat := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifnbitjmprefId
    codeCell? := some (mkIfnbitjmprefCodeCell idx target tailBytes)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkProbeCase
    (name : String)
    (idx : Nat)
    (x : Int)
    (below : Array Value := #[])
    (target : Cell := bodyEmpty) : OracleCase :=
  mkCase name idx (mkStack below x) target #[0x71]

private def runIfnbitjmprefDirect
    (idx : Nat)
    (stack : Array Value)
    (code : Slice := bodySliceEmpty) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfBitJmp (ifnbitjmprefInstr idx code) stack

private def runIfnbitjmprefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfBitJmp instr (VM.push (intV dispatchSentinel)) stack

private def runIfnbitjmprefRaw
    (idx : Nat)
    (stack : Array Value)
    (code : Slice := bodySliceEmpty)
    (cc : Continuation := .quit 0)
    (gasLimit : Int := 1_000_000) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      gas := GasLimits.ofLimits gasLimit gasLimit 0 }
  (execInstrFlowIfBitJmp (ifnbitjmprefInstr idx code) (pure ())).run st0

private def jumpTarget (code : Slice) : Continuation :=
  .ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty

def suite : InstrSuite where
  id := ifnbitjmprefId
  unit := #[
    { name := "unit/raw/branch-predicate-and-cc-updates"
      run := do
        let ccInit : Continuation := .quit 91
        let target := bodySlicePush7

        let (rTaken0, sTaken0) := runIfnbitjmprefRaw 0 (mkStack #[] 2) target ccInit
        match rTaken0 with
        | .error e =>
            throw (IO.userError s!"taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sTaken0.stack != #[intV 2] then
              throw (IO.userError s!"taken/idx0: stack mismatch {reprStr sTaken0.stack}")
            else if sTaken0.cc != jumpTarget target then
              throw (IO.userError s!"taken/idx0: cc mismatch {reprStr sTaken0.cc}")
            else
              pure ()

        let (rNotTaken0, sNotTaken0) := runIfnbitjmprefRaw 0 (mkStack #[] 1) target ccInit
        match rNotTaken0 with
        | .error e =>
            throw (IO.userError s!"not-taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sNotTaken0.stack != #[intV 1] then
              throw (IO.userError s!"not-taken/idx0: stack mismatch {reprStr sNotTaken0.stack}")
            else if sNotTaken0.cc != ccInit then
              throw (IO.userError s!"not-taken/idx0: cc should remain unchanged, got {reprStr sNotTaken0.cc}")
            else
              pure ()

        let (rTaken31, sTaken31) :=
          runIfnbitjmprefRaw 31 (mkStack #[] ((pow2 31) - 1)) target ccInit
        match rTaken31 with
        | .error e =>
            throw (IO.userError s!"taken/idx31: expected success, got {e}")
        | .ok _ =>
            if sTaken31.stack != #[intV ((pow2 31) - 1)] then
              throw (IO.userError s!"taken/idx31: stack mismatch {reprStr sTaken31.stack}")
            else if sTaken31.cc != jumpTarget target then
              throw (IO.userError s!"taken/idx31: cc mismatch {reprStr sTaken31.cc}")
            else
              pure ()

        let (rNotTaken31, sNotTaken31) :=
          runIfnbitjmprefRaw 31 (mkStack #[] (pow2 31)) target ccInit
        match rNotTaken31 with
        | .error e =>
            throw (IO.userError s!"not-taken/idx31: expected success, got {e}")
        | .ok _ =>
            if sNotTaken31.stack != #[intV (pow2 31)] then
              throw (IO.userError s!"not-taken/idx31: stack mismatch {reprStr sNotTaken31.stack}")
            else if sNotTaken31.cc != ccInit then
              throw (IO.userError s!"not-taken/idx31: cc should remain unchanged, got {reprStr sNotTaken31.cc}")
            else
              pure () }
    ,
    { name := "unit/error/pop-int-finite-site-stack-effects"
      run := do
        expectErr "underflow/empty" (runIfnbitjmprefDirect 0 #[]) .stkUnd
        expectErr "type/top-null" (runIfnbitjmprefDirect 0 #[.null]) .typeChk
        expectErr "type/top-cell" (runIfnbitjmprefDirect 0 #[.cell refCellA]) .typeChk
        expectErr "type/top-builder" (runIfnbitjmprefDirect 0 #[.builder Builder.empty]) .typeChk
        expectErr "type/top-slice" (runIfnbitjmprefDirect 0 #[.slice fullSliceA]) .typeChk
        expectErr "type/top-tuple" (runIfnbitjmprefDirect 0 #[.tuple #[]]) .typeChk

        let (rType, sType) := runIfnbitjmprefRaw 0 #[intV 88, .null] bodySliceEmpty (.quit 10)
        match rType with
        | .error .typeChk =>
            if sType.stack == #[intV 88] then
              pure ()
            else
              throw (IO.userError s!"pop-int/type: stack mismatch {reprStr sType.stack}")
        | .error e =>
            throw (IO.userError s!"pop-int/type: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "pop-int/type: expected typeChk, got success")

        let (rNan, sNan) := runIfnbitjmprefRaw 0 #[intV 99, .int .nan] bodySliceEmpty (.quit 10)
        match rNan with
        | .error .intOv =>
            if sNan.stack == #[intV 99] then
              pure ()
            else
              throw (IO.userError s!"pop-int/nan: stack mismatch {reprStr sNan.stack}")
        | .error e =>
            throw (IO.userError s!"pop-int/nan: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "pop-int/nan: expected intOv, got success") }
    ,
    { name := "unit/bit-semantics/signed-values"
      run := do
        let ccInit : Continuation := .quit 33
        let target := bodySlicePush7

        let (rNeg1, sNeg1) := runIfnbitjmprefRaw 0 (mkStack #[] (-1)) target ccInit
        match rNeg1 with
        | .error e =>
            throw (IO.userError s!"neg1/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg1.cc != ccInit then
              throw (IO.userError s!"neg1/idx0: expected no jump, got {reprStr sNeg1.cc}")
            else
              pure ()

        let (rNeg2Bit0, sNeg2Bit0) := runIfnbitjmprefRaw 0 (mkStack #[] (-2)) target ccInit
        match rNeg2Bit0 with
        | .error e =>
            throw (IO.userError s!"neg2/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit0.cc != jumpTarget target then
              throw (IO.userError s!"neg2/idx0: expected jump, got {reprStr sNeg2Bit0.cc}")
            else
              pure ()

        let (rNeg2Bit1, sNeg2Bit1) := runIfnbitjmprefRaw 1 (mkStack #[] (-2)) target ccInit
        match rNeg2Bit1 with
        | .error e =>
            throw (IO.userError s!"neg2/idx1: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit1.cc != ccInit then
              throw (IO.userError s!"neg2/idx1: expected no jump, got {reprStr sNeg2Bit1.cc}")
            else
              pure ()

        let (rMin257, sMin257) := runIfnbitjmprefRaw 31 (mkStack #[] minInt257) target ccInit
        match rMin257 with
        | .error e =>
            throw (IO.userError s!"min257/idx31: expected success, got {e}")
        | .ok _ =>
            if sMin257.cc != jumpTarget target then
              throw (IO.userError s!"min257/idx31: expected jump, got {reprStr sMin257.cc}")
            else
              pure () }
    ,
    { name := "unit/ref-load-gated-on-taken-branch"
      run := do
        let ccInit : Continuation := .quit 63

        let (rNoLoad, sNoLoad) := runIfnbitjmprefRaw 0 #[intV 1] bodySlicePush7 ccInit 0
        match rNoLoad with
        | .error e =>
            throw (IO.userError s!"no-load/not-taken: expected success, got {e}")
        | .ok _ =>
            if sNoLoad.stack != #[intV 1] then
              throw (IO.userError s!"no-load/not-taken: stack mismatch {reprStr sNoLoad.stack}")
            else if sNoLoad.cc != ccInit then
              throw (IO.userError s!"no-load/not-taken: cc mismatch {reprStr sNoLoad.cc}")
            else
              pure ()

        let (rLoad, sLoad) := runIfnbitjmprefRaw 0 #[intV 2] bodySlicePush7 ccInit 0
        match rLoad with
        | .error .outOfGas =>
            if sLoad.stack != #[intV 2] then
              throw (IO.userError s!"load/taken: stack mismatch {reprStr sLoad.stack}")
            else if sLoad.cc != ccInit then
              throw (IO.userError s!"load/taken: cc should remain unchanged, got {reprStr sLoad.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"load/taken: expected outOfGas, got {e}")
        | .ok _ =>
            throw (IO.userError "load/taken: expected outOfGas, got success") }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfnbitjmprefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match-ifnbitjmpref"
          (runIfnbitjmprefDispatchFallback (ifnbitjmprefInstr 0 bodySliceEmpty) #[intV 1])
          #[intV 1] }
  ]
  oracle := #[
    mkProbeCase "branch/taken/idx0/x0" 0 0,
    mkProbeCase "branch/taken/idx0/x2" 0 2,
    mkProbeCase "branch/taken/idx0/xneg2" 0 (-2),
    mkProbeCase "branch/taken/idx1/x1" 1 1,
    mkProbeCase "branch/taken/idx5/xpow4" 5 (pow2 4),
    mkProbeCase "branch/taken/idx5/x0" 5 0,
    mkProbeCase "branch/taken/idx31/xpow31minus1" 31 ((pow2 31) - 1),
    mkProbeCase "branch/taken/idx31/xmin257" 31 minInt257,
    mkProbeCase "branch/taken/deep-null-int" 0 2 #[.null, intV 9],
    mkProbeCase "branch/taken/deep-cell" 31 minInt257 #[.cell refCellA],

    mkProbeCase "branch/not-taken/idx0/x1" 0 1,
    mkProbeCase "branch/not-taken/idx0/xneg1" 0 (-1),
    mkProbeCase "branch/not-taken/idx1/x2" 1 2,
    mkProbeCase "branch/not-taken/idx1/xneg2" 1 (-2),
    mkProbeCase "branch/not-taken/idx5/xpow5" 5 (pow2 5),
    mkProbeCase "branch/not-taken/idx5/xpow5plus3" 5 ((pow2 5) + 3),
    mkProbeCase "branch/not-taken/idx31/xpow31" 31 (pow2 31),
    mkProbeCase "branch/not-taken/idx31/xneg1" 31 (-1),
    mkProbeCase "branch/not-taken/deep-null-int" 0 1 #[.null, intV 9],
    mkProbeCase "branch/not-taken/deep-builder-tuple" 31 (-1) #[.builder Builder.empty, .tuple #[]],

    mkCase "ok/no-tail/taken-default" 0 (mkStack #[] 0),
    mkCase "ok/no-tail/not-taken-default" 0 (mkStack #[] 1),
    mkCase "ok/no-tail/taken-idx31" 31 (mkStack #[] ((pow2 31) - 1)),
    mkCase "ok/no-tail/not-taken-idx31" 31 (mkStack #[] (pow2 31)),
    mkCase "ok/no-tail/deep-taken" 1 (mkStack #[.null, .cell refCellA] 1),
    mkCase "ok/no-tail/deep-not-taken" 1 (mkStack #[.slice fullSliceB, .tuple #[]] 2),

    mkCase "target/push7/taken-idx0-x0" 0 (mkStack #[] 0) bodyPush7,
    mkCase "target/push7/taken-idx0-x2" 0 (mkStack #[] 2) bodyPush7,
    mkCase "target/push7/not-taken-idx0-x1" 0 (mkStack #[] 1) bodyPush7,
    mkCase "target/push7/taken-idx31" 31 (mkStack #[] ((pow2 31) - 1)) bodyPush7,
    mkCase "target/push7/not-taken-idx31" 31 (mkStack #[] (pow2 31)) bodyPush7,
    mkCase "target/push7/deep-taken" 1 (mkStack #[.null] 1) bodyPush7,
    mkCase "target/push9/taken" 0 (mkStack #[] 0) bodyPush9,
    mkCase "target/push9/not-taken" 0 (mkStack #[] 1) bodyPush9,

    mkCase "underflow/empty" 0 #[],
    mkCase "type/top-null" 0 #[.null],
    mkCase "type/top-cell" 0 #[.cell refCellA],
    mkCase "type/top-builder" 0 #[.builder Builder.empty],
    mkCase "type/top-slice" 0 #[.slice fullSliceA],
    mkCase "type/top-tuple" 0 #[.tuple #[]],
    mkCase "type/pop-removes-top-null-with-below" 0 #[intV 9, .null],
    mkCase "type/pop-removes-top-cell-with-below" 0 #[intV 9, .cell refCellA]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.IFNBITJMPREF
