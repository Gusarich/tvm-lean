import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SAMEALT

private def sameAltId : InstrId := { name := "SAMEALT" }

private def sameAltInstr : Instr := .sameAlt

private def retAltInstr : Instr := .retAlt

private def dispatchSentinel : Int := 49137

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceA : Slice :=
  Slice.ofCell cellA

private def fullSliceB : Slice :=
  Slice.ofCell cellB

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0, .null, intV (-4), .cell cellB]

private def runSameAltFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSameAlt instr (VM.push (intV dispatchSentinel)) stack

private def runSameAltRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc)
    (instr : Instr := sameAltInstr) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrContSameAlt instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

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

private def expectDecodeSameAlt
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .sameAlt then
        throw (IO.userError s!"{label}: expected .sameAlt, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[sameAltInstr, retAltInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sameAltId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := sameAltId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, sameAltInstr, retAltInstr] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, sameAltInstr, retAltInstr] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    sameAltInstr, retAltInstr] ++ tail

private def sameAltTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def sameAltTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedfa >>> 1) 15) #[]

private def sameAltOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/c0-from-c1/",
    "ok/nargs",
    "err/nargs",
    "ok/captured/",
    "err/captured/",
    "err/decode/"
  ]

private def sameAltFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := sameAltOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := sameAltId
  unit := #[
    { name := "unit/dispatch/matched-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSameAltFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        expectOkStack "dispatch/matched-samealt-does-not-run-next"
          (runSameAltFallback sameAltInstr #[intV 9])
          #[intV 9]

        let st ← expectRawOk "dispatch/matched-samealt-raw"
          (runSameAltRaw #[intV 5])
        if st.stack != #[intV 5] then
          throw (IO.userError s!"dispatch/matched-samealt-raw: expected stack #[5], got {reprStr st.stack}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"dispatch/matched-samealt-raw: expected c0=quit0, got {reprStr st.regs.c0}")
        if st.regs.c1 != .quit 0 then
          throw (IO.userError s!"dispatch/matched-samealt-raw: expected c1=quit0, got {reprStr st.regs.c1}")
        if st.cc != defaultCc then
          throw (IO.userError s!"dispatch/matched-samealt-raw: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/raw/overwrite-c1-preserve-c0-and-cc"
      run := do
        let c0Init : Continuation := .quit 7
        let c1Init : Continuation := .quit 42
        let ccInit : Continuation := .quit 77
        let regs : Regs := { Regs.initial with c0 := c0Init, c1 := c1Init }
        let st ← expectRawOk "raw/overwrite-c1"
          (runSameAltRaw noiseA regs ccInit)
        if st.stack != noiseA then
          throw (IO.userError s!"raw/overwrite-c1: expected stack unchanged, got {reprStr st.stack}")
        if st.regs.c0 != c0Init then
          throw (IO.userError s!"raw/overwrite-c1: expected c0 preserved, got {reprStr st.regs.c0}")
        if st.regs.c1 != c0Init then
          throw (IO.userError s!"raw/overwrite-c1: expected c1 copied from c0, got {reprStr st.regs.c1}")
        if st.cc != ccInit then
          throw (IO.userError s!"raw/overwrite-c1: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/raw/complex-c0-copied-exactly"
      run := do
        let c0Complex : Continuation := .whileBody (.quit 2) (.quit 3) (.quit 4)
        let ccInit : Continuation := .quit 91
        let regs : Regs := { Regs.initial with c0 := c0Complex, c1 := .quit 99 }
        let st ← expectRawOk "raw/complex-c0"
          (runSameAltRaw noiseB regs ccInit)
        if st.stack != noiseB then
          throw (IO.userError s!"raw/complex-c0: expected stack unchanged, got {reprStr st.stack}")
        if st.regs.c0 != c0Complex then
          throw (IO.userError s!"raw/complex-c0: expected c0 preserved, got {reprStr st.regs.c0}")
        if st.regs.c1 != c0Complex then
          throw (IO.userError s!"raw/complex-c0: expected c1 copied from c0, got {reprStr st.regs.c1}")
        if st.cc != ccInit then
          throw (IO.userError s!"raw/complex-c0: expected cc unchanged, got {reprStr st.cc}") }
    ,
    { name := "unit/raw/no-stack-access"
      run := do
        let stEmpty ← expectRawOk "raw/no-stack-access/empty"
          (runSameAltRaw #[] { Regs.initial with c0 := .quit 11, c1 := .quit 12 })
        if stEmpty.stack != #[] then
          throw (IO.userError s!"raw/no-stack-access/empty: expected empty stack, got {reprStr stEmpty.stack}")
        if stEmpty.regs.c1 != .quit 11 then
          throw (IO.userError s!"raw/no-stack-access/empty: expected c1=quit11, got {reprStr stEmpty.regs.c1}")

        let stDeep ← expectRawOk "raw/no-stack-access/deep"
          (runSameAltRaw noiseC { Regs.initial with c0 := .quit 13, c1 := .quit 1 })
        if stDeep.stack != noiseC then
          throw (IO.userError s!"raw/no-stack-access/deep: expected stack unchanged, got {reprStr stDeep.stack}")
        if stDeep.regs.c1 != .quit 13 then
          throw (IO.userError s!"raw/no-stack-access/deep: expected c1=quit13, got {reprStr stDeep.regs.c1}") }
    ,
    { name := "unit/opcode/decode-and-truncated-prefix"
      run := do
        let assembled ←
          match assembleCp0 [sameAltInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/samealt failed: {reprStr e}")
        if assembled.bits = natToBits 0xedfa 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/samealt: expected 0xedfa, got {reprStr assembled.bits}")

        expectDecodeSameAlt "decode/samealt" (Cell.mkOrdinary (natToBits 0xedfa 16) #[])
        expectDecodeErr "decode/truncated-8" sameAltTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" sameAltTruncated15Code .invOpcode }
  ]
  oracle := #[
    -- Basic SAMEALT observed via RETALT: default c0=quit0 should force RETALT to quit0.
    mkCase "ok/basic/empty" #[],
    mkCase "ok/basic/int" #[intV 5],
    mkCase "ok/basic/null-int" #[.null, intV 9],
    mkCase "ok/basic/cell" #[.cell cellA],
    mkCase "ok/basic/slice" #[.slice fullSliceB],
    mkCase "ok/basic/builder" #[.builder Builder.empty],
    mkCase "ok/basic/tuple-empty" #[.tuple #[]],
    mkCase "ok/basic/cont-quit0" #[q0],
    mkCase "ok/basic/noise-a" noiseA,
    mkCase "ok/basic/noise-b" noiseB,
    mkCase "ok/basic/noise-c" noiseC,
    mkCase "ok/basic/trailing-push-skipped" #[intV 3] #[sameAltInstr, retAltInstr, .pushInt (.num 777)],
    mkCase "ok/basic/trailing-add-skipped" #[intV 6, intV 2] #[sameAltInstr, retAltInstr, .add],

    -- Set c0 from c1(quit1), then SAMEALT, then RETALT.
    mkCase "ok/c0-from-c1/empty" #[] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/int" #[intV 12] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/noise-a" noiseA (progSetC0FromC1),
    mkCase "ok/c0-from-c1/noise-b" noiseB (progSetC0FromC1),
    mkCase "ok/c0-from-c1/trailing-push-skipped" #[intV 4] (progSetC0FromC1 #[.pushInt (.num 111)]),
    mkCase "ok/c0-from-c1/trailing-add-skipped"
      #[intV 1, intV 2] (progSetC0FromC1 #[.add]),

    -- c0 nargs coverage via SETNUMVARARGS, then SAMEALT + RETALT.
    mkCase "ok/nargs0/empty" #[] (progSetC0Nargs 0),
    mkCase "ok/nargs0/noise-a" noiseA (progSetC0Nargs 0),
    mkCase "err/nargs1/empty-underflow" #[] (progSetC0Nargs 1),
    mkCase "ok/nargs1/one-int" #[intV 33] (progSetC0Nargs 1),
    mkCase "ok/nargs1/one-null" #[.null] (progSetC0Nargs 1),
    mkCase "err/nargs2/empty-underflow" #[] (progSetC0Nargs 2),
    mkCase "err/nargs2/one-underflow" #[intV 44] (progSetC0Nargs 2),
    mkCase "ok/nargs2/two-int" #[intV 4, intV 5] (progSetC0Nargs 2),
    mkCase "ok/nargs2/two-noise" #[.null, intV 5] (progSetC0Nargs 2),
    mkCase "err/nargs3/two-underflow" #[intV 2, intV 3] (progSetC0Nargs 3),
    mkCase "ok/nargs3/three-int" #[intV 1, intV 2, intV 3] (progSetC0Nargs 3),
    mkCase "ok/nargs1/trailing-skipped" #[intV 7] (progSetC0Nargs 1 #[.pushInt (.num 999)]),

    -- c0 captured-stack merge coverage via SETCONTVARARGS(copy=1), then SAMEALT + RETALT.
    mkCase "ok/captured/more-minus1/empty-init" #[] (progSetC0Captured 70 (-1)),
    mkCase "ok/captured/more-minus1/one-init" #[intV 9] (progSetC0Captured 71 (-1)),
    mkCase "ok/captured/more0/empty-init" #[] (progSetC0Captured 72 0),
    mkCase "err/captured/more1/empty-underflow" #[] (progSetC0Captured 73 1),
    mkCase "ok/captured/more1/one-init" #[intV 9] (progSetC0Captured 74 1),
    mkCase "err/captured/more2/one-underflow" #[intV 9] (progSetC0Captured 75 2),
    mkCase "ok/captured/more2/two-init" #[intV 1, intV 2] (progSetC0Captured 76 2),
    mkCase "ok/captured/more0/noise-init" noiseA (progSetC0Captured 77 0),
    mkCase "ok/captured/more0/trailing-skipped" #[intV 4]
      (progSetC0Captured 78 0 #[.pushInt (.num 1234)]),
    mkCase "ok/captured/more1/two-init" #[intV 8, intV 9] (progSetC0Captured 79 1),

    -- Decode errors around SAMEALT prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] sameAltTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] sameAltTruncated15Code
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile sameAltId sameAltFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.SAMEALT
