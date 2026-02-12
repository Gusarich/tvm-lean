import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RET

/-
RET branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/Ret.lean` (`execInstrFlowRet`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdb30 -> .ret`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.ret -> 0xdb30`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ret`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret`, `VmState::jump`, `VmState::adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.cpp` (`OrdCont::jump`, `ArgContExt::jump`)

Branch map covered by this suite:
1. dispatch: `.ret` handled vs non-`.ret` fallback to `next`.
2. RET core:
  - `c0` is extracted, reset to `quit(0)`, then jumped to;
  - jump-time `nargs`/captured-stack behavior comes from `VM.jump`.
3. ordering/error behavior:
  - `c0` reset must happen before jump-time `stkUnd`;
  - underflow must leave `cc` unchanged on the failing RET step.
4. jump-time closure branches:
  - plain continuation target (`quit` target, no stack shaping);
  - `nargs` truncation + underflow branches;
  - captured-stack merge, including `copy = -1` (`more = -1`) branch.
5. decode/assembly boundaries:
  - exact opcode `0xdb30`;
  - truncated 8/15-bit prefixes fail with `invOpcode`.

Mismatch found and fixed:
- Lean previously kept jump-applied `cdata` on active `cc`, so RET targets
  could re-apply captured-stack/nargs shaping on the next continuation step
  (notably duplicating captured stack when `nargs = -1`).
- C++ applies stack shaping in `adjust_jump_cont`; then `OrdCont::jump` /
  `ArgContExt::jump` only apply save-list/codepage transitions.
- Fixed in `VM.jump` by normalizing active `cc` to empty `cdata` after
  jump-time shaping is performed.
-/

private def retId : InstrId := { name := "RET" }

private def retInstr : Instr := .ret

private def dispatchSentinel : Int := 49111

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

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
  #[.cont (.quit 0), .null, intV (-4), .cell cellB]

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def c0Captured (captured : Array Value) (nargs : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := captured, nargs := nargs }

private def runRetFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRet instr (VM.push (intV dispatchSentinel)) stack

private def runRetRaw
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc)
    (instr : Instr := retInstr) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowRet instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

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

private def expectDecodeRet
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .ret then
        throw (IO.userError s!"{label}: expected .ret, got {reprStr instr}")
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
    (program : Array Instr := #[retInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .ret] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, .ret] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    .ret] ++ tail

private def retTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb30 >>> 1) 15) #[]

private def retOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/c0-from-c1/",
    "ok/nargs",
    "err/nargs",
    "ok/captured/",
    "err/captured/",
    "err/decode/"
  ]

private def retFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := retOracleFamilies
    mutationModes := #[0, 0, 0, 1, 1, 2, 2, 3, 3, 4]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := retId
  unit := #[
    { name := "unit/dispatch/ret-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        let st ← expectRawOk "dispatch/matched-ret"
          (runRetRaw #[intV 5])
        if st.stack != #[intV 5] then
          throw (IO.userError
            s!"dispatch/matched-ret: expected unchanged stack [5], got {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"dispatch/matched-ret: expected cc=quit0, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"dispatch/matched-ret: expected c0 reset to quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/order/c0-reset-before-jump-underflow"
      run := do
        let target : Continuation := c0NeedArgs 2
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawErr "ret/jump-underflow"
          (runRetRaw #[intV 9] regs) .stkUnd
        if st.stack != #[intV 9] then
          throw (IO.userError s!"ret/jump-underflow: expected stack [9], got {reprStr st.stack}")
        if st.cc != defaultCc then
          throw (IO.userError s!"ret/jump-underflow: expected cc unchanged, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"ret/jump-underflow: expected c0 reset to quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/closure-stack-merge-path"
      run := do
        let target : Continuation := c0Captured #[intV 100] 1
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawOk "ret/closure-stack-merge"
          (runRetRaw #[intV 4, intV 5] regs)
        if st.stack != #[intV 100, intV 5] then
          throw (IO.userError
            s!"ret/closure-stack-merge: expected [100,5], got {reprStr st.stack}")
        if st.cc != target then
          throw (IO.userError
            s!"ret/closure-stack-merge: expected jump to target continuation, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"ret/closure-stack-merge: expected c0 reset to quit0, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/closure-stack-more-minus1-pass-all"
      run := do
        let target : Continuation := c0Captured #[intV 88] (-1)
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawOk "ret/closure-stack-more-minus1"
          (runRetRaw #[intV 7, intV 8] regs)
        if st.stack != #[intV 88, intV 7, intV 8] then
          throw (IO.userError
            s!"ret/closure-stack-more-minus1: expected [88,7,8], got {reprStr st.stack}")
        if st.cc != target then
          throw (IO.userError
            s!"ret/closure-stack-more-minus1: expected jump to target continuation, got {reprStr st.cc}") }
    ,
    { name := "unit/opcode/decode-and-truncated-prefix"
      run := do
        let assembled ←
          match assembleCp0 [retInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/ret failed: {reprStr e}")
        if assembled.bits = natToBits 0xdb30 16 then
          pure ()
        else
          throw (IO.userError s!"opcode/ret: expected 0xdb30, got {reprStr assembled.bits}")

        expectDecodeRet "decode/ret" (Cell.mkOrdinary (natToBits 0xdb30 16) #[])
        expectDecodeErr "decode/truncated-8" retTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" retTruncated15Code .invOpcode }
  ]
  oracle := #[
    -- Basic RET with default c0=quit0.
    mkCase "ok/basic/empty" #[],
    mkCase "ok/basic/int" #[intV 5],
    mkCase "ok/basic/null-int" #[.null, intV 9],
    mkCase "ok/basic/cell" #[.cell cellA],
    mkCase "ok/basic/slice" #[.slice fullSliceB],
    mkCase "ok/basic/builder" #[.builder Builder.empty],
    mkCase "ok/basic/tuple-empty" #[.tuple #[]],
    mkCase "ok/basic/cont-quit0" #[.cont (.quit 0)],
    mkCase "ok/basic/noise-a" noiseA,
    mkCase "ok/basic/noise-b" noiseB,
    mkCase "ok/basic/noise-c" noiseC,
    mkCase "ok/basic/trailing-push-skipped" #[intV 3] #[retInstr, .pushInt (.num 777)],
    mkCase "ok/basic/trailing-add-skipped" #[intV 6, intV 2] #[retInstr, .add],

    -- Retarget c0 from c1 (quit1), then RET.
    mkCase "ok/c0-from-c1/empty" #[] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/int" #[intV 12] (progSetC0FromC1),
    mkCase "ok/c0-from-c1/noise-a" noiseA (progSetC0FromC1),
    mkCase "ok/c0-from-c1/noise-b" noiseB (progSetC0FromC1),
    mkCase "ok/c0-from-c1/trailing-push-skipped" #[intV 4] (progSetC0FromC1 #[.pushInt (.num 111)]),
    mkCase "ok/c0-from-c1/trailing-add-skipped"
      #[intV 1, intV 2] (progSetC0FromC1 #[.add]),

    -- c0 nargs branch coverage via SETNUMVARARGS.
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

    -- c0 closure-stack merge coverage via SETCONTVARARGS(copy=1).
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

    -- Decode errors around RET prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retTruncated15Code
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile retId retFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RET
