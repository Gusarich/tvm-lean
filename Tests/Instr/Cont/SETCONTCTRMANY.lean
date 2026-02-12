import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTCTRMANY

/-!
SETCONTCTRMANY branch map (Lean vs C++):
- C++ references:
  - `crypto/vm/contops.cpp` (`exec_setcont_ctr_many`)
  - `crypto/vm/continuation.cpp` (`ControlRegs::define`)
  - `crypto/vm/stack.cpp` (`Stack::pop_cont`)
- Lean references:
  - `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` (`.setContCtrMany`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popCont`)

Covered paths:
1. dispatch (`.contExt (.setContCtrMany mask)`) vs fallback;
2. decode boundaries for opcode `0xede3` (24-bit immediate) and nearby opcodes;
3. forbidden `c6` bit check (`mask & (1 << 6)`) before any stack pop;
4. `pop_cont` underflow/type behavior and stack-effect ordering;
5. define loop order `i = 0..7` with re-define failures on c0..c5;
6. c7 define semantics (existing c7 is preserved);
7. force-cdata wrapping for continuations without control data.
-/

private def setContCtrManyId : InstrId := { name := "SETCONTCTRMANY" }
private def setContCtrManyInstr (mask : Nat) : Instr := .contExt (.setContCtrMany mask)
private def dispatchSentinel : Int := 48663

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def sliceA : Slice := Slice.ofCell cellA

private def q0 : Value := .cont (.quit 0)

private def tupleA : Array Value := #[intV 17, .null]
private def tupleB : Array Value := #[intV 99]

private def contWithC0 : Value :=
  .cont (.ordinary (Slice.ofCell Cell.empty) (.quit 0)
    ({ OrdCregs.empty with c0 := some (.quit 9) }) OrdCdata.empty)

private def contWithC1 : Value :=
  .cont (.ordinary (Slice.ofCell Cell.empty) (.quit 0)
    ({ OrdCregs.empty with c1 := some (.quit 9) }) OrdCdata.empty)

private def contWithC5 : Value :=
  .cont (.ordinary (Slice.ofCell Cell.empty) (.quit 0)
    ({ OrdCregs.empty with c5 := some cellA }) OrdCdata.empty)

private def contWithC7 : Value :=
  .cont (.ordinary (Slice.ofCell Cell.empty) (.quit 0)
    ({ OrdCregs.empty with c7 := some tupleA }) OrdCdata.empty)

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell cellA, .slice sliceA]

private def noiseC : Array Value :=
  #[.builder Builder.empty, .tuple #[]]

private def mkStack (below : Array Value) (cont : Value) : Array Value :=
  below ++ #[cont]

private def runSetContCtrManyDirect (mask : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt (setContCtrManyInstr mask) stack

private def runSetContCtrManyFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetContCtrManyRaw
    (stack : Array Value)
    (mask : Nat)
    (regs : Regs := Regs.initial) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt (setContCtrManyInstr mask) (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeSetContCtrMany
    (label : String)
    (code : Cell)
    (expectedMask : Nat)
    (expectedBits : Nat := 24) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setContCtrManyInstr expectedMask then
        throw (IO.userError s!"{label}: expected {reprStr (setContCtrManyInstr expectedMask)}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def expectDecodeNotSetContCtrMany (label : String) (code : Cell) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, _, _) =>
      match instr with
      | .contExt (.setContCtrMany _) =>
          throw (IO.userError s!"{label}: expected different decode, got {reprStr instr}")
      | _ =>
          pure ()
  | .error _ =>
      pure ()

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrManyId
    program := program
    initStack := stack
    fuel := fuel }

private def mkMaskCase
    (name : String)
    (stack : Array Value)
    (mask : Nat)
    (tail : Array Instr := #[])
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack (#[setContCtrManyInstr mask] ++ tail) fuel

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrManyId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetThenSet (mask1 mask2 : Nat) : Array Instr :=
  #[setContCtrManyInstr mask1, setContCtrManyInstr mask2]

private def setContCtrManyCode (mask : Nat) : Cell :=
  let word24 : Nat := (0xede3 <<< 8) + (mask &&& 0xff)
  Cell.mkOrdinary (natToBits word24 24) #[]

private def setContCtrManyTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setContCtrManyTruncated16Code : Cell :=
  Cell.mkOrdinary (natToBits 0xede3 16) #[]

private def nearEde4Code : Cell :=
  Cell.mkOrdinary (natToBits 0xede4 16) #[]

private def nearEde2Code : Cell :=
  Cell.mkOrdinary (natToBits 0xede2 16) #[]

private def nearEde5Code : Cell :=
  Cell.mkOrdinary (natToBits 0xede5 16) #[]

private def oracleCases : Array OracleCase := #[
  -- Success masks over all allowed ctr bits.
  mkMaskCase "ok/basic/mask0/quit0" (mkStack #[] q0) 0,
  mkMaskCase "ok/basic/mask1/quit0" (mkStack #[] q0) 1,
  mkMaskCase "ok/basic/mask2/quit0" (mkStack #[] q0) 2,
  mkMaskCase "ok/basic/mask4/quit0" (mkStack #[] q0) 4,
  mkMaskCase "ok/basic/mask8/quit0" (mkStack #[] q0) 8,
  mkMaskCase "ok/basic/mask16/quit0" (mkStack #[] q0) 16,
  mkMaskCase "ok/basic/mask32/quit0" (mkStack #[] q0) 32,
  mkMaskCase "ok/basic/mask128/quit0" (mkStack #[] q0) 128,
  mkMaskCase "ok/basic/mask3/quit0" (mkStack #[] q0) 3,
  mkMaskCase "ok/basic/mask5/quit0" (mkStack #[] q0) 5,
  mkMaskCase "ok/basic/mask24/quit0" (mkStack #[] q0) 24,
  mkMaskCase "ok/basic/mask33/quit0" (mkStack #[] q0) 33,
  mkMaskCase "ok/basic/mask129/quit0" (mkStack #[] q0) 129,
  mkMaskCase "ok/basic/mask160/quit0" (mkStack #[] q0) 160,
  mkMaskCase "ok/basic/mask187/quit0" (mkStack #[] q0) 187,
  mkMaskCase "ok/noise/mask1" (mkStack noiseA q0) 1,
  mkMaskCase "ok/noise/mask128" (mkStack noiseB q0) 128,
  mkMaskCase "ok/noise/mask0" (mkStack noiseC q0) 0,
  mkCase "ok/nonordinary/mask0" #[.slice sliceA]
    #[.blessArgs 0 0, setContCtrManyInstr 0],
  mkCase "ok/nonordinary/mask1" #[.slice sliceA]
    #[.blessArgs 0 0, setContCtrManyInstr 1],
  mkCase "ok/nonordinary/mask128" #[.slice sliceA]
    #[.blessArgs 0 0, setContCtrManyInstr 128],
  mkMaskCase "ok/flow/tail-push-runs" (mkStack #[] q0) 0 #[.pushInt (.num 777)],
  mkMaskCase "ok/flow/tail-popctr0-runs" (mkStack #[intV 9] q0) 1 #[.popCtr 0],
  mkCase "ok/reapply/mask128-then-mask128" (mkStack #[] q0) (progSetThenSet 128 128),
  mkCase "ok/reapply/mask1-then-mask0" (mkStack #[] q0) (progSetThenSet 1 0),

  -- Re-define failures and loop-order coverage.
  mkCase "err/reapply/mask1-then-mask1" (mkStack #[] q0) (progSetThenSet 1 1),
  mkCase "err/reapply/mask2-then-mask3-fails-at-i1" (mkStack #[] q0) (progSetThenSet 2 3),
  mkCase "err/reapply/mask32-then-mask33-fails-at-i5" (mkStack #[] q0) (progSetThenSet 32 33),
  mkCase "err/reapply/mask1-then-mask129-fails-at-i0-before-i7" (mkStack #[] q0) (progSetThenSet 1 129),

  -- Underflow/type errors.
  mkMaskCase "err/underflow/empty/mask0" #[] 0,
  mkMaskCase "err/underflow/empty/mask1" #[] 1,
  mkMaskCase "err/cont-type/null" (mkStack #[] .null) 1,
  mkMaskCase "err/cont-type/cell" (mkStack #[] (.cell cellA)) 1,
  mkMaskCase "err/cont-type/slice" (mkStack #[] (.slice sliceA)) 1,
  mkMaskCase "err/cont-type/int" (mkStack #[] (intV 7)) 1,
  mkMaskCase "err/cont-type/tuple" (mkStack #[] (.tuple #[])) 1,
  mkMaskCase "err/cont-type/builder" (mkStack #[] (.builder Builder.empty)) 1,

  -- Forbidden c6 mask bit.
  mkMaskCase "err/mask-range/bit6-only" (mkStack #[] q0) 64,
  mkMaskCase "err/mask-range/bit6-with-low-bits" (mkStack #[] q0) 127,
  mkMaskCase "err/mask-range/bit6-with-high-bit" (mkStack #[] q0) 192,
  mkMaskCase "err/mask-range/bit6-max255" (mkStack #[] q0) 255,

  -- Ordering-sensitive probes.
  mkMaskCase "err/order/range-before-cont-type" (mkStack #[] .null) 64,
  mkMaskCase "err/order/range-before-underflow" #[] 64,
  mkMaskCase "err/order/cont-type-after-pop" (mkStack #[intV 8] .null) 1,

  -- Decode/raw opcode boundaries.
  mkCodeCase "ok/raw/opcode-ede3-mask0" (mkStack #[] q0) (setContCtrManyCode 0),
  mkCodeCase "ok/raw/opcode-ede3-mask63" (mkStack #[] q0) (setContCtrManyCode 63),
  mkCodeCase "err/raw/opcode-ede3-mask64-range" (mkStack #[] q0) (setContCtrManyCode 64),
  mkCodeCase "err/raw/opcode-truncated8" (mkStack #[] q0) setContCtrManyTruncated8Code,
  mkCodeCase "err/raw/opcode-truncated16" (mkStack #[] q0) setContCtrManyTruncated16Code,
  mkCodeCase "err/raw/opcode-near-ede4" (mkStack #[] q0) nearEde4Code,
  mkCodeCase "err/raw/opcode-near-ede2" (mkStack #[] q0) nearEde2Code,
  mkCodeCase "err/raw/opcode-near-ede5" (mkStack #[] q0) nearEde5Code
]

private def setContCtrManyOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/noise/",
    "ok/nonordinary/",
    "ok/flow/",
    "ok/reapply/",
    "ok/raw/",
    "err/reapply/",
    "err/underflow/",
    "err/cont-type/",
    "err/mask-range/",
    "err/order/",
    "err/raw/"
  ]

private def setContCtrManyFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := setContCtrManyOracleFamilies
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := setContCtrManyId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetContCtrManyFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-op"
          (runSetContCtrManyFallback (setContCtrManyInstr 0) (mkStack #[] q0))
          #[q0] }
    ,
    { name := "unit/decode/exact-truncated-near"
      run := do
        expectDecodeSetContCtrMany "decode/exact-mask0" (setContCtrManyCode 0) 0
        expectDecodeSetContCtrMany "decode/exact-mask63" (setContCtrManyCode 63) 63
        expectDecodeErr "decode/truncated-8" setContCtrManyTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-16" setContCtrManyTruncated16Code .invOpcode
        expectDecodeNotSetContCtrMany "decode/near-ede4-not-many" nearEde4Code
        expectDecodeNotSetContCtrMany "decode/near-ede2-not-many" nearEde2Code
        expectDecodeNotSetContCtrMany "decode/near-ede5-not-many" nearEde5Code }
    ,
    { name := "unit/errors/class-sanity"
      run := do
        expectErr "underflow/empty" (runSetContCtrManyDirect 0 #[]) .stkUnd
        expectErr "mask/range-bit6" (runSetContCtrManyDirect 64 (mkStack #[] q0)) .rangeChk
        expectErr "cont/type-null" (runSetContCtrManyDirect 1 (mkStack #[] .null)) .typeChk
        expectErr "cont/type-cell" (runSetContCtrManyDirect 1 (mkStack #[] (.cell cellA))) .typeChk }
    ,
    { name := "unit/order/range-before-pop"
      run := do
        let st ← expectRawErr "range-before-pop"
          (runSetContCtrManyRaw (mkStack #[intV 8] .null) 64) .rangeChk
        if st.stack != #[intV 8, .null] then
          throw (IO.userError
            s!"range-before-pop: expected stack #[8,null], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/range-before-underflow"
      run := do
        let st ← expectRawErr "range-before-underflow"
          (runSetContCtrManyRaw #[] 64) .rangeChk
        if st.stack != #[] then
          throw (IO.userError
            s!"range-before-underflow: expected empty stack, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/cont-type-after-pop"
      run := do
        let st ← expectRawErr "cont-type-after-pop"
          (runSetContCtrManyRaw (mkStack #[intV 5] .null) 1) .typeChk
        if st.stack != #[intV 5] then
          throw (IO.userError
            s!"cont-type-after-pop: expected remaining #[5], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/mask0-preserves-nonordinary"
      run := do
        let st ← expectRawOk "mask0-preserves-nonordinary"
          (runSetContCtrManyRaw (mkStack #[] (.cont (.quit 37))) 0)
        if st.stack != #[.cont (.quit 37)] then
          throw (IO.userError
            s!"mask0-preserves-nonordinary: expected #[quit37], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/nonzero-wraps-and-defines-c0"
      run := do
        let st ← expectRawOk "nonzero-wraps-and-defines-c0"
          (runSetContCtrManyRaw (mkStack #[] (.cont (.quit 37))) 1)
        match st.stack with
        | #[.cont (.envelope ext cregs cdata)] =>
            if ext != .quit 37 then
              throw (IO.userError s!"nonzero-wraps: expected ext=quit37, got {reprStr ext}")
            else if cregs.c0 != some (.quit 0) then
              throw (IO.userError s!"nonzero-wraps: expected c0=quit0, got {reprStr cregs.c0}")
            else if cregs.c1.isSome || cregs.c2.isSome || cregs.c3.isSome
                || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
              throw (IO.userError s!"nonzero-wraps: unexpected extra cregs {reprStr cregs}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError s!"nonzero-wraps: unexpected cdata {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"nonzero-wraps: expected envelope stack, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/define-c7-keeps-existing"
      run := do
        let regs1 : Regs := { Regs.initial with c7 := tupleB }
        let st ← expectRawOk "define-c7-keeps-existing"
          (runSetContCtrManyRaw (mkStack #[] contWithC7) 128 regs1)
        match st.stack with
        | #[.cont (.ordinary _ _ cregs cdata)] =>
            if cregs.c7 != some tupleA then
              throw (IO.userError
                s!"define-c7-keeps-existing: expected c7={reprStr tupleA}, got {reprStr cregs.c7}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError s!"define-c7-keeps-existing: unexpected cdata {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"define-c7-keeps-existing: unexpected stack shape {reprStr st.stack}") }
    ,
    { name := "unit/raw/redefine-c0-fails-after-pop"
      run := do
        let st ← expectRawErr "redefine-c0-fails"
          (runSetContCtrManyRaw (mkStack #[intV 44] contWithC0) 1) .typeChk
        if st.stack != #[intV 44] then
          throw (IO.userError
            s!"redefine-c0-fails: expected remaining #[44], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/redefine-order-fails-at-i1-after-i0"
      run := do
        let st ← expectRawErr "redefine-order-fails-at-i1"
          (runSetContCtrManyRaw (mkStack #[intV 55] contWithC1) 3) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError
            s!"redefine-order-fails-at-i1: expected remaining #[55], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/redefine-order-fails-at-i5-after-i0"
      run := do
        let st ← expectRawErr "redefine-order-fails-at-i5"
          (runSetContCtrManyRaw (mkStack #[intV 66] contWithC5) 33) .typeChk
        if st.stack != #[intV 66] then
          throw (IO.userError
            s!"redefine-order-fails-at-i5: expected remaining #[66], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    mkContMutationFuzzSpecWithProfile
      setContCtrManyId
      setContCtrManyFuzzProfile
      500
  ]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRMANY
