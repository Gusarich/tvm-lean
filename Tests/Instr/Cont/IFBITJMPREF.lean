import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFBITJMPREF

/-
IFBITJMPREF branch map (Lean vs C++ `exec_if_bit_jmpref`):
- decode/ref gate: cp0 decode must read one ref operand; missing ref => `invOpcode`
  before any stack checks (`Cp0.takeRefInv` mirrors C++ `!cs.have_refs()` path).
- pop/int path: execution pops finite int (`pop_int_finite`) from stack top,
  computes bit `(args & 0x1f)`, then re-pushes the same integer.
- error mapping/order at pop-int site:
  - empty stack => `stkUnd`;
  - non-int => `typeChk` (top consumed);
  - NaN => `intOv` (top consumed).
- branch predicate: jump iff extracted bit is `true` (`IFBITJMPREF`, non-negated form).
- jump target: the decoded ref is turned into ordinary continuation and entered via `VM.jump`.
- ref-load gas: cell-load registration happens only on taken branch.
-/

private def ifbitjmprefId : InstrId := { name := "IFBITJMPREF" }

private def ifbitjmprefInstr (idx : Nat) (code : Slice) : Instr :=
  .contExt (.ifbitjmpref idx code)

private def dispatchSentinel : Int := 48731

private def tailMarker : Int := 7

private def refLeafA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refLeafB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refLeafA]

private def fullSliceA : Slice :=
  Slice.ofCell refLeafA

private def fullSliceB : Slice :=
  Slice.ofCell refLeafB

private def jumpBodyCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x71 8) #[]

private def jumpBodyCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x72 8) #[]

private def jumpBodySliceA : Slice :=
  Slice.ofCell jumpBodyCellA

private def jumpBodySliceB : Slice :=
  Slice.ofCell jumpBodyCellB

private def jumpBodyContA : Continuation :=
  .ordinary jumpBodySliceA (.quit 0) OrdCregs.empty OrdCdata.empty

private def jumpBodyContB : Continuation :=
  .ordinary jumpBodySliceB (.quit 0) OrdCregs.empty OrdCdata.empty

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def ifbitjmprefWord (idx : Nat) : Nat :=
  0xe3c0 + (idx &&& 0x1f)

private def mkIfbitjmprefCodeCell
    (idx : Nat)
    (body : Cell)
    (tailBytes : Array Nat := #[0x77]) : Cell :=
  Cell.mkOrdinary (natToBits (ifbitjmprefWord idx) 16 ++ bytesToBits tailBytes) #[body]

private def mkIfbitjmprefNanPrefixCodeCell
    (idx : Nat)
    (body : Cell)
    (tailBytes : Array Nat := #[0x77]) : Cell :=
  -- 0x83ff = PUSHNAN
  Cell.mkOrdinary
    (natToBits 0x83ff 16 ++ natToBits (ifbitjmprefWord idx) 16 ++ bytesToBits tailBytes)
    #[body]

private def mkIfbitjmprefMissingRefCodeCell
    (idx : Nat)
    (tailBytes : Array Nat := #[0x77]) : Cell :=
  Cell.mkOrdinary (natToBits (ifbitjmprefWord idx) 16 ++ bytesToBits tailBytes) #[]

private def mkIfbitjmprefStack
    (below : Array Value)
    (x : Int) : Array Value :=
  below ++ #[intV x]

private def mkCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (body : Cell := jumpBodyCellA)
    (tailBytes : Array Nat := #[0x77])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifbitjmprefId
    codeCell? := some (mkIfbitjmprefCodeCell idx body tailBytes)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkNanCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (body : Cell := jumpBodyCellA)
    (tailBytes : Array Nat := #[0x77])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifbitjmprefId
    codeCell? := some (mkIfbitjmprefNanPrefixCodeCell idx body tailBytes)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkMissingRefCase
    (name : String)
    (idx : Nat)
    (stack : Array Value)
    (tailBytes : Array Nat := #[0x77])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifbitjmprefId
    codeCell? := some (mkIfbitjmprefMissingRefCodeCell idx tailBytes)
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkProbeCase
    (name : String)
    (idx : Nat)
    (x : Int)
    (below : Array Value := #[])
    (body : Cell := jumpBodyCellA)
    (tailBytes : Array Nat := #[0x77]) : OracleCase :=
  mkCase name idx (mkIfbitjmprefStack below x) body tailBytes

private def runIfbitjmprefDirect
    (idx : Nat)
    (stack : Array Value)
    (code : Slice := jumpBodySliceA) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfBitJmp (ifbitjmprefInstr idx code) stack

private def runIfbitjmprefDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfBitJmp instr (VM.push (intV dispatchSentinel)) stack

private def runIfbitjmprefRaw
    (idx : Nat)
    (stack : Array Value)
    (code : Slice := jumpBodySliceA)
    (cc : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  (execInstrFlowIfBitJmp (ifbitjmprefInstr idx code) (pure ())).run st0

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected {expectedBits} bits, got {bits}")
      else
        pure s'

def suite : InstrSuite where
  id := ifbitjmprefId
  unit := #[
    { name := "unit/raw/branch-predicate-updates-cc-stack-and-loads"
      run := do
        let ccInit : Continuation := .quit 93
        let expectedHashA := Cell.hashBytes jumpBodyCellA

        let (rTaken0, sTaken0) := runIfbitjmprefRaw 0 (mkIfbitjmprefStack #[] 1) jumpBodySliceA ccInit
        match rTaken0 with
        | .error e => throw (IO.userError s!"taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sTaken0.stack != #[intV 1] then
              throw (IO.userError s!"taken/idx0: stack mismatch {reprStr sTaken0.stack}")
            else if sTaken0.cc != jumpBodyContA then
              throw (IO.userError s!"taken/idx0: cc mismatch {reprStr sTaken0.cc}")
            else if sTaken0.loadedCells != #[expectedHashA] then
              throw (IO.userError s!"taken/idx0: loadedCells mismatch {reprStr sTaken0.loadedCells}")
            else
              pure ()

        let (rNotTaken0, sNotTaken0) := runIfbitjmprefRaw 0 (mkIfbitjmprefStack #[] 2) jumpBodySliceA ccInit
        match rNotTaken0 with
        | .error e => throw (IO.userError s!"not-taken/idx0: expected success, got {e}")
        | .ok _ =>
            if sNotTaken0.stack != #[intV 2] then
              throw (IO.userError s!"not-taken/idx0: stack mismatch {reprStr sNotTaken0.stack}")
            else if sNotTaken0.cc != ccInit then
              throw (IO.userError s!"not-taken/idx0: cc should remain unchanged, got {reprStr sNotTaken0.cc}")
            else if sNotTaken0.loadedCells != #[] then
              throw (IO.userError s!"not-taken/idx0: expected no loaded cells, got {reprStr sNotTaken0.loadedCells}")
            else
              pure ()

        let (rTaken31, sTaken31) :=
          runIfbitjmprefRaw 31 (mkIfbitjmprefStack #[] (pow2 31)) jumpBodySliceB ccInit
        match rTaken31 with
        | .error e => throw (IO.userError s!"taken/idx31: expected success, got {e}")
        | .ok _ =>
            if sTaken31.stack != #[intV (pow2 31)] then
              throw (IO.userError s!"taken/idx31: stack mismatch {reprStr sTaken31.stack}")
            else if sTaken31.cc != jumpBodyContB then
              throw (IO.userError s!"taken/idx31: cc mismatch {reprStr sTaken31.cc}")
            else
              pure () }
    ,
    { name := "unit/error/pop-int-finite-site-stack-effects"
      run := do
        let (rUnd, sUnd) := runIfbitjmprefRaw 0 #[] jumpBodySliceA (.quit 11)
        match rUnd with
        | .error .stkUnd =>
            if sUnd.stack == #[] then
              pure ()
            else
              throw (IO.userError s!"underflow/empty-stack-mutated: {reprStr sUnd.stack}")
        | .error e =>
            throw (IO.userError s!"underflow/empty: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "underflow/empty: expected stkUnd, got success")

        let (rTypeNull, sTypeNull) := runIfbitjmprefRaw 0 #[intV 88, .null] jumpBodySliceA (.quit 11)
        match rTypeNull with
        | .error .typeChk =>
            if sTypeNull.stack == #[intV 88] then
              pure ()
            else
              throw (IO.userError s!"type/null: stack mismatch {reprStr sTypeNull.stack}")
        | .error e =>
            throw (IO.userError s!"type/null: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/null: expected typeChk, got success")

        let (rTypeCell, sTypeCell) := runIfbitjmprefRaw 0 #[intV 5, .cell refLeafA] jumpBodySliceA (.quit 11)
        match rTypeCell with
        | .error .typeChk =>
            if sTypeCell.stack == #[intV 5] then
              pure ()
            else
              throw (IO.userError s!"type/cell: stack mismatch {reprStr sTypeCell.stack}")
        | .error e =>
            throw (IO.userError s!"type/cell: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/cell: expected typeChk, got success")

        let (rNan, sNan) := runIfbitjmprefRaw 0 #[intV 99, .int .nan] jumpBodySliceA (.quit 11)
        match rNan with
        | .error .intOv =>
            if sNan.stack == #[intV 99] then
              pure ()
            else
              throw (IO.userError s!"intov/nan: stack mismatch {reprStr sNan.stack}")
        | .error e =>
            throw (IO.userError s!"intov/nan: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "intov/nan: expected intOv, got success") }
    ,
    { name := "unit/bit-semantics/signed-values"
      run := do
        let ccInit : Continuation := .quit 44

        let (rNeg1, sNeg1) := runIfbitjmprefRaw 0 (mkIfbitjmprefStack #[] (-1)) jumpBodySliceA ccInit
        match rNeg1 with
        | .error e => throw (IO.userError s!"neg1/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg1.cc != jumpBodyContA then
              throw (IO.userError "neg1/idx0: expected jump")
            else
              pure ()

        let (rNeg2Bit0, sNeg2Bit0) := runIfbitjmprefRaw 0 (mkIfbitjmprefStack #[] (-2)) jumpBodySliceA ccInit
        match rNeg2Bit0 with
        | .error e => throw (IO.userError s!"neg2/idx0: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit0.cc != ccInit then
              throw (IO.userError "neg2/idx0: expected no jump")
            else
              pure ()

        let (rNeg2Bit1, sNeg2Bit1) := runIfbitjmprefRaw 1 (mkIfbitjmprefStack #[] (-2)) jumpBodySliceA ccInit
        match rNeg2Bit1 with
        | .error e => throw (IO.userError s!"neg2/idx1: expected success, got {e}")
        | .ok _ =>
            if sNeg2Bit1.cc != jumpBodyContA then
              throw (IO.userError "neg2/idx1: expected jump")
            else
              pure ()

        let (rMin257Bit31, sMin257Bit31) :=
          runIfbitjmprefRaw 31 (mkIfbitjmprefStack #[] minInt257) jumpBodySliceA ccInit
        match rMin257Bit31 with
        | .error e => throw (IO.userError s!"min257/idx31: expected success, got {e}")
        | .ok _ =>
            if sMin257Bit31.cc != ccInit then
              throw (IO.userError "min257/idx31: expected no jump")
            else
              pure () }
    ,
    { name := "unit/decode/ref-consumption-and-missing-ref"
      run := do
        let codeOk : Cell := mkIfbitjmprefCodeCell 5 jumpBodyCellA #[0x77, 0x71]
        let s0 : Slice := Slice.ofCell codeOk
        let s1 ← expectDecodeStep "decode/ifbitjmpref"
          s0
          (ifbitjmprefInstr 5 jumpBodySliceA)
          16

        if s1.refsRemaining != 0 then
          throw (IO.userError s!"decode/ifbitjmpref: expected refsRemaining=0, got {s1.refsRemaining}")

        let s2 ← expectDecodeStep "decode/tail/push7"
          s1
          (.pushInt (.num tailMarker))
          8

        let _ ← expectDecodeStep "decode/tail/push1"
          s2
          (.pushInt (.num 1))
          8

        let codeMissing : Cell := mkIfbitjmprefMissingRefCodeCell 0 #[0x77]
        match decodeCp0WithBits (Slice.ofCell codeMissing) with
        | .error .invOpcode => pure ()
        | .error e =>
            throw (IO.userError s!"decode/missing-ref: expected invOpcode, got {e}")
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"decode/missing-ref: expected error, got instr={reprStr instr} bits={bits}") }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfbitjmprefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]

        expectOkStack "dispatch/match-ifbitjmpref"
          (runIfbitjmprefDispatchFallback
            (ifbitjmprefInstr 0 jumpBodySliceA)
            (mkIfbitjmprefStack #[] 0))
          #[intV 0] }
  ]
  oracle := #[
    mkProbeCase "branch/taken/idx0/x1" 0 1,
    mkProbeCase "branch/taken/idx0/xneg1" 0 (-1),
    mkProbeCase "branch/taken/idx1/x2" 1 2,
    mkProbeCase "branch/taken/idx1/xneg2" 1 (-2),
    mkProbeCase "branch/taken/idx5/xpow5" 5 (pow2 5),
    mkProbeCase "branch/taken/idx5/xpow5plus3" 5 ((pow2 5) + 3),
    mkProbeCase "branch/taken/idx31/xpow31" 31 (pow2 31),
    mkProbeCase "branch/taken/idx31/xneg2" 31 (-2),
    mkProbeCase "branch/taken/deep-null-int" 0 1 #[.null, intV 9],
    mkProbeCase "branch/taken/deep-cell" 1 2 #[.cell refLeafA],
    mkProbeCase "branch/taken/deep-slice-builder" 5 (pow2 5) #[.slice fullSliceA, .builder Builder.empty],
    mkProbeCase "branch/taken/alt-body-cell" 0 1 #[] jumpBodyCellB,

    mkProbeCase "branch/not-taken/idx0/x0" 0 0,
    mkProbeCase "branch/not-taken/idx0/x2" 0 2,
    mkProbeCase "branch/not-taken/idx1/x1" 1 1,
    mkProbeCase "branch/not-taken/idx5/xpow4" 5 (pow2 4),
    mkProbeCase "branch/not-taken/idx5/x0" 5 0,
    mkProbeCase "branch/not-taken/idx31/xpow31minus1" 31 ((pow2 31) - 1),
    mkProbeCase "branch/not-taken/idx31/xmin257" 31 minInt257,
    mkProbeCase "branch/not-taken/deep-null-int" 0 0 #[.null, intV 9],
    mkProbeCase "branch/not-taken/deep-cell" 31 minInt257 #[.cell refLeafA],
    mkProbeCase "branch/not-taken/deep-builder-tuple" 1 1 #[.builder Builder.empty, .tuple #[]],
    mkProbeCase "branch/not-taken/deep-slice" 5 0 #[.slice fullSliceB],
    mkProbeCase "branch/not-taken/alt-body-cell" 31 ((pow2 31) - 1) #[] jumpBodyCellB,

    mkCase "ok/no-tail/taken-default" 0 (mkIfbitjmprefStack #[] 1) jumpBodyCellA #[],
    mkCase "ok/no-tail/not-taken-default" 0 (mkIfbitjmprefStack #[] 0) jumpBodyCellA #[],
    mkCase "ok/no-tail/deep-preserve" 31 (mkIfbitjmprefStack #[.slice fullSliceB, .tuple #[]] ((pow2 31) - 1)) jumpBodyCellA #[],
    mkCase "ok/no-tail/taken-alt-body" 1 (mkIfbitjmprefStack #[.null] 2) jumpBodyCellB #[],
    mkCase "ok/no-tail/not-taken-alt-body" 1 (mkIfbitjmprefStack #[.null] 1) jumpBodyCellB #[],
    mkCase "ok/no-tail/taken-minimal-stack" 5 (mkIfbitjmprefStack #[] (pow2 5)) jumpBodyCellA #[],

    mkCase "underflow/empty" 0 #[],
    mkCase "type/popint/null-top" 0 #[.null],
    mkCase "type/popint/cell-top" 0 #[.cell refLeafA],
    mkCase "type/popint/builder-top" 0 #[.builder Builder.empty],
    mkCase "type/popint/slice-top" 0 #[.slice fullSliceA],
    mkCase "type/popint/tuple-top" 0 #[.tuple #[]],
    mkCase "type/popint/cont-top" 0 #[.cont (.quit 0)],
    mkCase "type/popint/top-null-with-below" 0 #[intV 5, .null],
    mkCase "type/popint/top-cell-with-below" 31 #[intV (-9), .cell refLeafB],

    mkNanCase "intov/popint/nan-via-prefix" 0 #[],
    mkNanCase "intov/popint/nan-via-prefix-with-below" 31 #[intV 42],

    mkMissingRefCase "invopcode/missing-ref/empty-stack" 0 #[],
    mkMissingRefCase "invopcode/missing-ref/int-top" 0 #[intV 1],
    mkMissingRefCase "invopcode/missing-ref/null-top" 0 #[.null],
    mkMissingRefCase "invopcode/missing-ref/deep-stack" 5 #[.null, intV 9, intV 1],
    mkMissingRefCase "invopcode/missing-ref/type-vs-ref-order" 1 #[.cell refLeafA],
    mkMissingRefCase "invopcode/missing-ref/tuple-top" 31 #[.tuple #[]]
  ]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.IFBITJMPREF
