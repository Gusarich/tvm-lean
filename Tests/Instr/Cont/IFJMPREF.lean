import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.IFJMPREF

/-
IFJMPREF branch map (Lean vs C++ `exec_if_jmpref`):
- C++ path: `exec_do_with_cell` decodes embedded ref, then lambda executes
  `pop_bool ? jump(ref_to_cont(cell)) : 0`.
- Decode-level branches (cp0 `0xe302`):
  - success with one embedded ref;
  - `invOpcode` on missing/truncated opcode/ref.
- Exec-level branches:
  - `popBool` success vs `.stkUnd` / `.typeChk` / `.intOv`;
  - bool=false => no jump, no cell-load registration;
  - bool=true => register cell load, then jump to ref continuation.
- Jump semantics parity:
  - C++ uses `VmState::jump`; Lean now uses `VM.jump` (not raw `jumpTo`).
  - For `ref_to_cont`/`.ordinary code ... OrdCdata.empty`, this is the simple-jump branch,
    but using `VM.jump` preserves semantic parity with C++ control-flow entrypoint.
-/

private def ifjmprefId : InstrId := { name := "IFJMPREF" }

private def ifjmprefOpcode : Nat := 0xe302

private def dispatchSentinel : Int := 41077

private def targetEmpty : Cell :=
  Cell.empty

private def targetPush1 : Cell :=
  Cell.mkOrdinary (natToBits 0x71 8) #[]

private def targetPush2 : Cell :=
  Cell.mkOrdinary (natToBits 0x72 8) #[]

private def refLeaf : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[]

private def refBranch : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[refLeaf]

private def fullSliceBranch : Slice :=
  Slice.ofCell refBranch

private def ifjmprefInstr (target : Cell := targetEmpty) : Instr :=
  .ifjmpref (Slice.ofCell target)

private def bytesToBits (bytes : Array Nat) : BitString :=
  bytes.foldl (fun acc b => acc ++ natToBits (b % 256) 8) #[]

private def mkCodeCell (bytes : Array Nat) (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary (bytesToBits bytes) refs

private def mkIfjmprefCodeCell (target : Cell) (tailBytes : Array Nat := #[]) : Cell :=
  mkCodeCell (#[0xe3, 0x02] ++ tailBytes) #[target]

private def mkIfjmprefNanCodeCell (target : Cell := targetEmpty) : Cell :=
  -- PUSHINT NaN (0x83ff), then IFJMPREF.
  mkCodeCell #[0x83, 0xff, 0xe3, 0x02] #[target]

private def missingRefCode : Cell :=
  mkCodeCell #[0xe3, 0x02] #[]

private def truncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits ifjmprefOpcode 16).take 15) #[targetEmpty]

private def oneBytePrefixCode : Cell :=
  mkCodeCell #[0xe3] #[targetEmpty]

private def emptyCode : Cell :=
  Cell.empty

private def tailPush1 : Array Nat :=
  #[0x71]

private def tailPush2 : Array Nat :=
  #[0x72]

private def tailAdd : Array Nat :=
  #[0xa0]

private def tailRetAlt : Array Nat :=
  #[0xdb, 0x31]

private def withFlag (below : Array Value) (flag : Int) : Array Value :=
  below ++ #[intV flag]

private def mkCase
    (name : String)
    (stack : Array Value)
    (codeCell : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ifjmprefId
    codeCell? := some codeCell
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkIfjmprefCase
    (name : String)
    (flag : Int)
    (below : Array Value := #[])
    (target : Cell := targetEmpty)
    (tailBytes : Array Nat := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name (withFlag below flag) (mkIfjmprefCodeCell target tailBytes) gasLimits fuel

private def runIfjmprefDirect (target : Cell) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowIfjmpref (ifjmprefInstr target) stack

private def runIfjmprefDispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowIfjmpref instr (VM.push (intV dispatchSentinel)) stack

private def runIfjmprefOnState (target : Cell) (st0 : VmState) : Except Excno Unit × VmState :=
  (execInstrFlowIfjmpref (ifjmprefInstr target) (pure ())).run st0

private def runIfjmprefRaw
    (target : Cell)
    (stack : Array Value)
    (cc : Continuation := .quit 0)
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc, gas := gas }
  runIfjmprefOnState target st0

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

private def regsEq (x y : Regs) : Bool :=
  x.c0 == y.c0 && x.c1 == y.c1 && x.c2 == y.c2 && x.c3 == y.c3 &&
  x.c4 == y.c4 && x.c5 == y.c5 && x.c7 == y.c7

private def ifjmprefOracleFamilies : Array String :=
  #[
    "taken/",
    "not-taken/",
    "underflow/",
    "type/",
    "intov/",
    "decode/"
  ]

private def ifjmprefFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := ifjmprefOracleFamilies
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      2, 2,
      3, 3, 3,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := ifjmprefId
  unit := #[
    { name := "unit/direct/taken-vs-not-taken-pop-bool"
      run := do
        let below : Array Value := #[.null, intV 9]
        expectOkStack "taken/pop-one-preserve-below"
          (runIfjmprefDirect targetEmpty (withFlag below 1))
          below
        expectOkStack "not-taken/pop-one-preserve-below"
          (runIfjmprefDirect targetEmpty (withFlag below 0))
          below }
    ,
    { name := "unit/raw/cc-transition-and-control-regs"
      run := do
        let base : VmState := VmState.initial Cell.empty
        let regsCustom : Regs :=
          { base.regs with
            c0 := .quit 10
            c1 := .quit 11
            c2 := .quit 12
            c3 := .quit 13 }
        let ccInit : Continuation := .quit 91

        let stTaken0 : VmState :=
          { base with stack := withFlag #[intV 5] 1, cc := ccInit, regs := regsCustom }
        let (rTaken, sTaken) := runIfjmprefOnState targetPush1 stTaken0
        match rTaken with
        | .error e =>
            throw (IO.userError s!"taken/raw: expected success, got {e}")
        | .ok _ =>
            let expectedCc : Continuation :=
              .ordinary (Slice.ofCell targetPush1) (.quit 0) OrdCregs.empty OrdCdata.empty
            if sTaken.stack != #[intV 5] then
              throw (IO.userError s!"taken/raw: stack mismatch {reprStr sTaken.stack}")
            else if sTaken.cc != expectedCc then
              throw (IO.userError s!"taken/raw: cc mismatch {reprStr sTaken.cc}")
            else if !(regsEq sTaken.regs regsCustom) then
              throw (IO.userError s!"taken/raw: regs changed {reprStr sTaken.regs}")
            else
              pure ()

        let stNotTaken0 : VmState :=
          { base with stack := withFlag #[intV 6] 0, cc := ccInit, regs := regsCustom }
        let (rNotTaken, sNotTaken) := runIfjmprefOnState targetPush1 stNotTaken0
        match rNotTaken with
        | .error e =>
            throw (IO.userError s!"not-taken/raw: expected success, got {e}")
        | .ok _ =>
            if sNotTaken.stack != #[intV 6] then
              throw (IO.userError s!"not-taken/raw: stack mismatch {reprStr sNotTaken.stack}")
            else if sNotTaken.cc != ccInit then
              throw (IO.userError s!"not-taken/raw: cc changed {reprStr sNotTaken.cc}")
            else if !(regsEq sNotTaken.regs regsCustom) then
              throw (IO.userError s!"not-taken/raw: regs changed {reprStr sNotTaken.regs}")
            else
              pure () }
    ,
    { name := "unit/error/underflow-type-intov-and-pop-effects"
      run := do
        expectErr "underflow/empty" (runIfjmprefDirect targetEmpty #[]) .stkUnd
        expectErr "type/null" (runIfjmprefDirect targetEmpty #[.null]) .typeChk
        expectErr "intov/nan" (runIfjmprefDirect targetEmpty #[.int .nan]) .intOv

        let (rType, sType) := runIfjmprefRaw targetEmpty #[intV 77, .null] (.quit 10)
        match rType with
        | .error .typeChk =>
            if sType.stack == #[intV 77] then
              pure ()
            else
              throw (IO.userError s!"type/pop-effect: stack mismatch {reprStr sType.stack}")
        | .error e =>
            throw (IO.userError s!"type/pop-effect: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "type/pop-effect: expected typeChk, got success")

        let (rNan, sNan) := runIfjmprefRaw targetEmpty #[intV 88, .int .nan] (.quit 10)
        match rNan with
        | .error .intOv =>
            if sNan.stack == #[intV 88] then
              pure ()
            else
              throw (IO.userError s!"nan/pop-effect: stack mismatch {reprStr sNan.stack}")
        | .error e =>
            throw (IO.userError s!"nan/pop-effect: expected intOv, got {e}")
        | .ok _ =>
            throw (IO.userError "nan/pop-effect: expected intOv, got success") }
    ,
    { name := "unit/gas/taken-load-can-oom-not-taken-skips-load"
      run := do
        let tight : GasLimits := GasLimits.ofLimit 99
        let ccInit : Continuation := .quit 7

        let (rTaken, sTaken) := runIfjmprefRaw targetPush1 (withFlag #[intV 4] 1) ccInit tight
        match rTaken with
        | .error .outOfGas =>
            if sTaken.stack != #[intV 4] then
              throw (IO.userError s!"taken/oom: stack mismatch {reprStr sTaken.stack}")
            else if sTaken.cc != ccInit then
              throw (IO.userError s!"taken/oom: cc changed {reprStr sTaken.cc}")
            else
              pure ()
        | .error e =>
            throw (IO.userError s!"taken/oom: expected outOfGas, got {e}")
        | .ok _ =>
            throw (IO.userError "taken/oom: expected outOfGas, got success")

        let (rNotTaken, sNotTaken) := runIfjmprefRaw targetPush1 (withFlag #[intV 4] 0) ccInit tight
        match rNotTaken with
        | .error e =>
            throw (IO.userError s!"not-taken/tight: expected success, got {e}")
        | .ok _ =>
            if sNotTaken.stack != #[intV 4] then
              throw (IO.userError s!"not-taken/tight: stack mismatch {reprStr sNotTaken.stack}")
            else if sNotTaken.cc != ccInit then
              throw (IO.userError s!"not-taken/tight: cc changed {reprStr sNotTaken.cc}")
            else
              pure () }
    ,
    { name := "unit/decode/success-and-errors"
      run := do
        let sOk := Slice.ofCell (mkIfjmprefCodeCell targetEmpty)
        match decodeCp0WithBits sOk with
        | .error e =>
            throw (IO.userError s!"decode/ok: expected success, got {e}")
        | .ok (instr, bits, rest) =>
            if instr != .ifjmpref (Slice.ofCell targetEmpty) then
              throw (IO.userError s!"decode/ok: instr mismatch {reprStr instr}")
            else if bits != 16 then
              throw (IO.userError s!"decode/ok: expected 16 bits, got {bits}")
            else if rest.refPos != 1 then
              throw (IO.userError s!"decode/ok: expected refPos=1, got {rest.refPos}")
            else
              pure ()

        expectDecodeErr "decode/missing-ref" (Slice.ofCell missingRefCode) .invOpcode
        expectDecodeErr "decode/truncated-15" (Slice.ofCell truncated15Code) .invOpcode
        expectDecodeErr "decode/one-byte-prefix" (Slice.ofCell oneBytePrefixCode) .invOpcode
        expectDecodeErr "decode/empty" (Slice.ofCell emptyCode) .invOpcode }
    ,
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runIfjmprefDispatchFallback .add #[.null])
          #[.null, intV dispatchSentinel]
        expectOkStack "dispatch/match-ifjmpref"
          (runIfjmprefDispatchFallback (ifjmprefInstr targetEmpty) #[intV 0])
          #[] }
  ]
  oracle := #[
    mkIfjmprefCase "taken/flag-1/skip-tail-push1" 1 #[] targetEmpty tailPush1,
    mkIfjmprefCase "taken/flag-neg1/skip-tail-push1" (-1) #[] targetEmpty tailPush1,
    mkIfjmprefCase "taken/flag-42/skip-tail-push1" 42 #[] targetEmpty tailPush1,
    mkIfjmprefCase "taken/flag-min257/skip-tail-push1" minInt257 #[] targetEmpty tailPush1,
    mkIfjmprefCase "taken/flag-pow2-255/skip-tail-push1" (pow2 255) #[] targetEmpty tailPush1,
    mkIfjmprefCase "taken/deep/null-int" 1 #[.null, intV 9] targetEmpty tailPush1,
    mkIfjmprefCase "taken/deep/cell" 1 #[.cell refBranch] targetEmpty tailPush1,
    mkIfjmprefCase "taken/deep/slice" 1 #[.slice fullSliceBranch] targetEmpty tailPush1,
    mkIfjmprefCase "taken/deep/builder-tuple" 1 #[.builder Builder.empty, .tuple #[]] targetEmpty tailPush1,
    mkIfjmprefCase "taken/tail-add-skipped" 1 #[intV 2, intV 3] targetEmpty tailAdd,
    mkIfjmprefCase "taken/tail-retalt-skipped" 1 #[] targetEmpty tailRetAlt,
    mkIfjmprefCase "taken/target-push1-runs" 1 #[intV 5] targetPush1 #[],
    mkIfjmprefCase "taken/target-push2-runs" 1 #[intV 6] targetPush2 #[],

    mkIfjmprefCase "not-taken/flag-0/tail-push1" 0 #[] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/flag-0/no-tail" 0,
    mkIfjmprefCase "not-taken/deep/null-int" 0 #[.null, intV 9] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/deep/cell" 0 #[.cell refBranch] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/deep/slice" 0 #[.slice fullSliceBranch] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/deep/builder-tuple" 0 #[.builder Builder.empty, .tuple #[]] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/deep/maxint" 0 #[intV maxInt257] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/deep/minplus1" 0 #[intV (minInt257 + 1)] targetEmpty tailPush1,
    mkIfjmprefCase "not-taken/tail-add-exec" 0 #[intV 2, intV 3] targetEmpty tailAdd,
    mkIfjmprefCase "not-taken/tail-retalt-exec" 0 #[] targetEmpty tailRetAlt,

    mkCase "underflow/empty" #[] (mkIfjmprefCodeCell targetEmpty),

    mkCase "type/bool-null" #[.null] (mkIfjmprefCodeCell targetEmpty),
    mkCase "type/bool-cell" #[.cell refBranch] (mkIfjmprefCodeCell targetEmpty),
    mkCase "type/bool-builder" #[.builder Builder.empty] (mkIfjmprefCodeCell targetEmpty),
    mkCase "type/bool-slice" #[.slice fullSliceBranch] (mkIfjmprefCodeCell targetEmpty),
    mkCase "type/bool-tuple" #[.tuple #[]] (mkIfjmprefCodeCell targetEmpty),
    mkCase "type/bool-cont" #[.cont (.quit 0)] (mkIfjmprefCodeCell targetEmpty),

    mkCase "intov/bool-nan-via-program" #[] (mkIfjmprefNanCodeCell targetEmpty),
    mkCase "intov/bool-nan-with-below-via-program" #[intV 9] (mkIfjmprefNanCodeCell targetEmpty),

    mkCase "decode/missing-ref" #[] missingRefCode,
    mkCase "decode/truncated-15bits" #[intV 1] truncated15Code,
    mkCase "decode/one-byte-prefix" #[] oneBytePrefixCode,
    mkCase "decode/empty-code" #[intV 1] emptyCode
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile ifjmprefId ifjmprefFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.IFJMPREF
