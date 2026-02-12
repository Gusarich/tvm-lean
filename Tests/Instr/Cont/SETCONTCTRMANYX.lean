import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETCONTCTRMANYX

/-
SETCONTCTRMANYX branch map (Lean vs C++):
- C++ references:
  - `crypto/vm/contops.cpp` (`exec_setcont_ctr_many_var`)
  - `crypto/vm/stack.cpp` (`pop_smallint_range`)
- Lean references:
  - `TvmLean/Semantics/Exec/Cont/ChangeExt.lean` (`.setContCtrManyX`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.popNatUpTo`)

Covered paths:
1. dispatch (`.contExt .setContCtrManyX` vs fallback);
2. `check_underflow(2)` entry gate;
3. mask pop/type/range mapping (`pop_smallint_range(255)` parity);
4. c6 rejection (`mask & (1 << 6)` => `rangeChk`) before cont pop;
5. continuation pop/type gate;
6. define loop order `i=0..7` including re-define failures;
7. force-cregs wrapping for continuations without cdata;
8. c7 define semantics (existing c7 preserved, no overwrite);
9. decode boundaries for `0xede4` and nearby invalid/truncated forms.
-/

private def setContCtrManyXId : InstrId := { name := "SETCONTCTRMANYX" }
private def setContCtrManyXInstr : Instr := .contExt .setContCtrManyX
private def dispatchSentinel : Int := 48664

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

private def mkStack (below : Array Value) (cont : Value) (mask : Int) : Array Value :=
  below ++ #[cont, intV mask]

private def runSetContCtrManyXDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContChangeExt setContCtrManyXInstr stack

private def runSetContCtrManyXFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContChangeExt instr (VM.push (intV dispatchSentinel)) stack

private def runSetContCtrManyXRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (instr : Instr := setContCtrManyXInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, regs := regs }
  (execInstrContChangeExt instr (pure ())).run st0

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

private def expectDecodeSetContCtrManyX
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != setContCtrManyXInstr then
        throw (IO.userError s!"{label}: expected {reprStr setContCtrManyXInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[setContCtrManyXInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrManyXId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setContCtrManyXId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetManyX (tail : Array Instr := #[]) : Array Instr :=
  #[setContCtrManyXInstr] ++ tail

private def progSetThenSet (mask2 : Int) : Array Instr :=
  #[setContCtrManyXInstr, .pushInt (.num mask2), setContCtrManyXInstr]

private def setContCtrManyXCode : Cell :=
  Cell.mkOrdinary (natToBits 0xede4 16) #[]

private def setContCtrManyXTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setContCtrManyXTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xede4 >>> 1) 15) #[]

private def setContCtrManyMissingArgCode : Cell :=
  Cell.mkOrdinary (natToBits 0xede3 16) #[]

private def nearEde5Code : Cell :=
  Cell.mkOrdinary (natToBits 0xede5 16) #[]

private def nearEddfCode : Cell :=
  Cell.mkOrdinary (natToBits 0xeddf 16) #[]

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def oracleCases : Array OracleCase := #[
  -- Success matrix over supported masks.
  mkCase "ok/basic/mask0/quit0" (mkStack #[] q0 0),
  mkCase "ok/basic/mask1/quit0" (mkStack #[] q0 1),
  mkCase "ok/basic/mask2/quit0" (mkStack #[] q0 2),
  mkCase "ok/basic/mask4/quit0" (mkStack #[] q0 4),
  mkCase "ok/basic/mask8/quit0" (mkStack #[] q0 8),
  mkCase "ok/basic/mask16/quit0" (mkStack #[] q0 16),
  mkCase "ok/basic/mask32/quit0" (mkStack #[] q0 32),
  mkCase "ok/basic/mask128/quit0" (mkStack #[] q0 128),
  mkCase "ok/basic/mask3/quit0" (mkStack #[] q0 3),
  mkCase "ok/basic/mask5/quit0" (mkStack #[] q0 5),
  mkCase "ok/basic/mask24/quit0" (mkStack #[] q0 24),
  mkCase "ok/basic/mask33/quit0" (mkStack #[] q0 33),
  mkCase "ok/basic/mask159/quit0" (mkStack #[] q0 159),
  mkCase "ok/basic/mask191/quit0" (mkStack #[] q0 191),
  mkCase "ok/noise/mask1" (mkStack noiseA q0 1),
  mkCase "ok/noise/mask128" (mkStack noiseB q0 128),
  mkCase "ok/noise/mask0" (mkStack noiseC q0 0),
  mkCase "ok/nonordinary/mask0" #[.slice sliceA]
    #[.blessArgs 0 0, .pushInt (.num 0), setContCtrManyXInstr],
  mkCase "ok/nonordinary/mask1" #[.slice sliceA]
    #[.blessArgs 0 0, .pushInt (.num 1), setContCtrManyXInstr],
  mkCase "ok/nonordinary/mask128" #[.slice sliceA]
    #[.blessArgs 0 0, .pushInt (.num 128), setContCtrManyXInstr],
  mkCase "ok/flow/tail-push-runs" (mkStack #[] q0 0)
    (progSetManyX #[.pushInt (.num 777)]),
  mkCase "ok/flow/tail-popctr0-runs" (mkStack #[intV 9] q0 1)
    (progSetManyX #[.popCtr 0]),
  mkCase "ok/reapply/mask128-then-mask128" (mkStack #[] q0 128)
    (progSetThenSet 128),
  mkCase "ok/reapply/mask1-then-mask0" (mkStack #[] q0 1)
    (progSetThenSet 0),

  -- Re-define failures and loop-order coverage.
  mkCase "err/reapply/mask1-then-mask1" (mkStack #[] q0 1)
    (progSetThenSet 1),
  mkCase "err/reapply/mask2-then-mask3-fails-at-i1" (mkStack #[] q0 2)
    (progSetThenSet 3),
  mkCase "err/reapply/mask32-then-mask33-fails-at-i5" (mkStack #[] q0 32)
    (progSetThenSet 33),
  mkCase "err/reapply/mask1-then-mask129-fails-at-i0-before-i7" (mkStack #[] q0 1)
    (progSetThenSet 129),

  -- Underflow and mask decoding failures.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one-int" #[intV 1],
  mkCase "err/underflow/one-cont" #[q0],
  mkCase "err/mask-type/null" #[q0, .null],
  mkCase "err/mask-type/cell" #[q0, .cell cellA],
  mkCase "err/mask-type/slice" #[q0, .slice sliceA],
  mkCase "err/mask-type/builder" #[q0, .builder Builder.empty],
  mkCase "err/mask-type/tuple" #[q0, .tuple #[]],
  mkCase "err/mask-type/cont" #[q0] #[.pushCtr 1, setContCtrManyXInstr],
  mkCase "err/mask-range/minus1" #[q0, intV (-1)],
  mkCase "err/mask-range/minus2" #[q0, intV (-2)],
  mkCase "err/mask-range/256" #[q0, intV 256],
  mkCase "err/mask-range/300" #[q0, intV 300],
  mkCase "err/mask-range/max-int257" #[q0, intV maxInt257],
  mkCase "err/mask-range/min-int257" #[q0, intV minInt257],
  mkCase "err/mask-range/nan-via-program" #[q0]
    #[.pushInt .nan, setContCtrManyXInstr],

  -- c6 rejection (`rangeChk`) and ordering before cont pop.
  mkCase "err/mask-range/bit6-only" #[q0, intV 64],
  mkCase "err/mask-range/bit6-with-low-bits" #[q0, intV 127],
  mkCase "err/mask-range/bit6-with-high-bit" #[q0, intV 192],

  -- Continuation type checks (after mask passes).
  mkCase "err/cont-type/null" #[.null, intV 1],
  mkCase "err/cont-type/cell" #[.cell cellA, intV 1],
  mkCase "err/cont-type/slice" #[.slice sliceA, intV 1],
  mkCase "err/cont-type/int" #[intV 7, intV 1],

  -- Explicit error-order probes.
  mkCase "err/order/range-before-cont-type" (mkStack #[] .null 256),
  mkCase "err/order/bit6-before-cont-type" (mkStack #[] .null 64),
  mkCase "err/order/mask-type-before-cont-type" #[.null, .null],

  -- Decode/raw opcode boundaries.
  mkCodeCase "ok/raw/opcode-ede4" (mkStack #[] q0 0) setContCtrManyXCode,
  mkCodeCase "err/raw/opcode-truncated8" (mkStack #[] q0 0) setContCtrManyXTruncated8Code,
  mkCodeCase "err/raw/opcode-truncated15" (mkStack #[] q0 0) setContCtrManyXTruncated15Code,
  mkCodeCase "err/raw/opcode-missing-tail-ede3" (mkStack #[] q0 0) setContCtrManyMissingArgCode,
  mkCodeCase "err/raw/opcode-near-ede5" (mkStack #[] q0 0) nearEde5Code,
  mkCodeCase "err/raw/opcode-near-eddf" (mkStack #[] q0 0) nearEddfCode
]

private def setContCtrManyXOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/noise/",
    "ok/nonordinary/",
    "ok/flow/",
    "ok/reapply/",
    "err/reapply/",
    "err/underflow/",
    "err/mask-type/",
    "err/mask-range/",
    "err/cont-type/",
    "err/order/",
    "ok/raw/",
    "err/raw/"
  ]

private def setContCtrManyXFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := setContCtrManyXOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def fuzzOkMaskPool : Array Int := #[0, 1, 2, 3, 4, 5, 8, 16, 32, 33, 128, 159, 191]

private def fuzzBadMaskPool : Array Int := #[-1, -2, 64, 96, 192, 256]

private def fuzzNoisePool : Array (Array Value) := #[#[], noiseA, noiseB, noiseC]

private def genSetContCtrManyXFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 7
  let (mask, rng2) := pickFromPool fuzzOkMaskPool rng1
  let (badMask, rng3) := pickFromPool fuzzBadMaskPool rng2
  let (noise, rng4) := pickFromPool fuzzNoisePool rng3
  let (case0, rngTag) :=
    if shape = 0 then
      (mkCase s!"fuzz/ok/basic/mask{mask}" (mkStack noise q0 mask), rng4)
    else if shape = 1 then
      (mkCase s!"fuzz/ok/flow/mask{mask}-tail-push"
        (mkStack #[] q0 mask) (progSetManyX #[.pushInt (.num 777)]), rng4)
    else if shape = 2 then
      (mkCase "fuzz/err/underflow/empty" #[], rng4)
    else if shape = 3 then
      (mkCase s!"fuzz/err/mask/range-{badMask}" (mkStack #[] q0 badMask), rng4)
    else if shape = 4 then
      (mkCase "fuzz/err/reapply/mask1-then-mask1" (mkStack #[] q0 1) (progSetThenSet 1), rng4)
    else if shape = 5 then
      let (rawCode, rng5) := pickFromPool #[setContCtrManyXCode] rng4
      (mkCodeCase "fuzz/ok/raw-opcode" (mkStack #[] q0 mask) rawCode, rng5)
    else if shape = 6 then
      let (rawCode, rng5) := pickFromPool
        #[setContCtrManyXTruncated8Code, setContCtrManyXTruncated15Code, setContCtrManyMissingArgCode,
          nearEde5Code, nearEddfCode] rng4
      (mkCodeCase "fuzz/err/raw-opcode" (mkStack #[] q0 mask) rawCode, rng5)
    else
      (mkCase "fuzz/err/mask-type/null" #[q0, .null], rng4)
  let (tag, rng5) := randNat rngTag 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng5)

def suite : InstrSuite where
  id := setContCtrManyXId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetContCtrManyXFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-op"
          (runSetContCtrManyXFallback setContCtrManyXInstr (mkStack #[] q0 0))
          #[q0] }
    ,
    { name := "unit/decode/exact-and-truncated"
      run := do
        expectDecodeSetContCtrManyX "decode/exact" setContCtrManyXCode
        expectDecodeErr "decode/truncated-8" setContCtrManyXTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" setContCtrManyXTruncated15Code .invOpcode
        expectDecodeErr "decode/missing-tail-ede3" setContCtrManyMissingArgCode .invOpcode }
    ,
    { name := "unit/errors/class-sanity"
      run := do
        expectErr "underflow/empty" (runSetContCtrManyXDirect #[]) .stkUnd
        expectErr "mask/type-null" (runSetContCtrManyXDirect #[q0, .null]) .typeChk
        expectErr "mask/range-minus1" (runSetContCtrManyXDirect #[q0, intV (-1)]) .rangeChk
        expectErr "mask/range-256" (runSetContCtrManyXDirect #[q0, intV 256]) .rangeChk
        expectErr "mask/range-bit6" (runSetContCtrManyXDirect #[q0, intV 64]) .rangeChk
        expectErr "cont/type-null" (runSetContCtrManyXDirect #[.null, intV 1]) .typeChk }
    ,
    { name := "unit/order/underflow-before-mask-type"
      run := do
        expectErr "underflow-before-mask-type" (runSetContCtrManyXDirect #[.null]) .stkUnd }
    ,
    { name := "unit/order/range-before-cont-type-and-mask-pop"
      run := do
        let st ← expectRawErr "range-before-cont-type"
          (runSetContCtrManyXRaw (mkStack #[intV 8] .null 256)) .rangeChk
        if st.stack != #[intV 8, .null] then
          throw (IO.userError
            s!"range-before-cont-type: expected stack #[8,null], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/bit6-before-cont-type-and-mask-pop"
      run := do
        let st ← expectRawErr "bit6-before-cont-type"
          (runSetContCtrManyXRaw (mkStack #[] .null 64)) .rangeChk
        if st.stack != #[.null] then
          throw (IO.userError
            s!"bit6-before-cont-type: expected stack #[null], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/cont-type-after-mask-pop"
      run := do
        let st ← expectRawErr "cont-type-after-mask-pop"
          (runSetContCtrManyXRaw (mkStack #[intV 5] .null 0)) .typeChk
        if st.stack != #[intV 5] then
          throw (IO.userError
            s!"cont-type-after-mask-pop: expected remaining #[5], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/mask0-preserves-nonordinary"
      run := do
        let st ← expectRawOk "mask0-preserves-nonordinary"
          (runSetContCtrManyXRaw (mkStack #[] (.cont (.quit 37)) 0))
        if st.stack != #[.cont (.quit 37)] then
          throw (IO.userError
            s!"mask0-preserves-nonordinary: expected #[quit37], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/nonzero-wraps-and-defines-c0"
      run := do
        let st ← expectRawOk "nonzero-wraps-and-defines-c0"
          (runSetContCtrManyXRaw (mkStack #[] (.cont (.quit 37)) 1))
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
          (runSetContCtrManyXRaw (mkStack #[] contWithC7 128) regs1)
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
    { name := "unit/raw/redefine-c0-fails-after-popping-mask-and-cont"
      run := do
        let st ← expectRawErr "redefine-c0-fails"
          (runSetContCtrManyXRaw (mkStack #[intV 44] contWithC0 1)) .typeChk
        if st.stack != #[intV 44] then
          throw (IO.userError
            s!"redefine-c0-fails: expected remaining #[44], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/redefine-order-fails-at-i1-after-i0"
      run := do
        let st ← expectRawErr "redefine-order-fails-at-i1"
          (runSetContCtrManyXRaw (mkStack #[intV 55] contWithC1 3)) .typeChk
        if st.stack != #[intV 55] then
          throw (IO.userError
            s!"redefine-order-fails-at-i1: expected remaining #[55], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/raw/redefine-order-fails-at-i5-after-i0"
      run := do
        let st ← expectRawErr "redefine-order-fails-at-i5"
          (runSetContCtrManyXRaw (mkStack #[intV 66] contWithC5 33)) .typeChk
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
    { seed := fuzzSeedForInstr setContCtrManyXId
      count := 500
      gen := genSetContCtrManyXFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRMANYX
