import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.INVERT

/-!
INVERT parity map (Lean vs C++):
- Lean: `TvmLean/Semantics/Exec/Cont/AtExit.lean` (`.contExt .invert`)
- C++: `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_invert`)

Expected behavior:
1. swap only control registers `c0` and `c1`;
2. no stack reads/writes, so no underflow/type errors;
3. no jump/cc rewrite;
4. decode opcode is exactly `0xedf8` (16 bits).
-/

private def invertId : InstrId := { name := "INVERT" }
private def invertInstr : Instr := .contExt .invert
private def dispatchSentinel : Int := 52917

private def q0 : Continuation := .quit 0
private def q1 : Continuation := .quit 1
private def q7 : Continuation := .quit 7
private def q9 : Continuation := .quit 9

private def q0V : Value := .cont q0

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0xa5 8) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x5a 8) #[refCellA]

private def sliceA : Slice := Slice.ofCell refCellA
private def sliceB : Slice := Slice.ofCell refCellB

private def ordContA : Continuation :=
  .ordinary sliceA q0 OrdCregs.empty OrdCdata.empty

private def envContB : Continuation :=
  .envelope q1 ({ OrdCregs.empty with c0 := some q7 }) OrdCdata.empty

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def invertRawCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf8 16) #[]

private def invertTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def invertTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf8 >>> 1) 15) #[]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[invertInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := invertId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := invertId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def runInvertDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContAtExit invertInstr stack

private def runInvertDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContAtExit instr (VM.push (intV dispatchSentinel)) stack

private def runInvertRaw
    (stack : Array Value)
    (c0 : Continuation := q0)
    (c1 : Continuation := q1)
    (c2 : Continuation := .excQuit)
    (c3 : Continuation := .quit 11)
    (cc : Continuation := defaultCc)
    (instr : Instr := invertInstr)
    (next : VM Unit := pure ()) : Prod (Except Excno Unit) VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { regs0 with c0 := c0, c1 := c1, c2 := c2, c3 := c3 }
      cc := cc }
  (execInstrContAtExit instr next).run st0

private def expectRawOk (label : String) (out : Prod (Except Excno Unit) VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

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

private def expectDecodeInvert
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != invertInstr then
        throw (IO.userError s!"{label}: expected {reprStr invertInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def progSetC1OrdAInvertPushC0 : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 1, invertInstr, .pushCtr 0]

private def progSetC0OrdAInvertPushC1 : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 0, invertInstr, .pushCtr 1]

private def progSetC1OrdAInvertPushC1 : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 1, invertInstr, .pushCtr 1]

private def progSetC0OrdAInvertPushC0 : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 0, invertInstr, .pushCtr 0]

private def progSetC1OrdBInvertPushC0 : Array Instr :=
  #[.pushRefCont refCellB, .popCtr 1, invertInstr, .pushCtr 0]

private def progBlessSetC1InvertPushC0 : Array Instr :=
  #[.bless, .popCtr 1, invertInstr, .pushCtr 0]

private def progBlessSetC0InvertPushC1 : Array Instr :=
  #[.bless, .popCtr 0, invertInstr, .pushCtr 1]

private def progBuildEnvelopeToC1InvertPushC0 : Array Instr :=
  #[.pushCtr 0, .pushCtr 0, .boolAnd, .popCtr 1, invertInstr, .pushCtr 0]

private def progBuildEnvelopeToC0InvertPushC1 : Array Instr :=
  #[.pushCtr 0, .pushCtr 0, .boolAnd, .popCtr 0, invertInstr, .pushCtr 1]

private def progBuildEnvelopeToC1DoubleInvertPushC1 : Array Instr :=
  #[.pushCtr 0, .pushCtr 0, .boolAnd, .popCtr 1, invertInstr, invertInstr, .pushCtr 1]

private def progSetBothInvertPushBoth : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 0, .pushRefCont refCellB, .popCtr 1, invertInstr, .pushCtr 0, .pushCtr 1]

private def progSetBothDoubleInvertPushBoth : Array Instr :=
  #[.pushRefCont refCellA, .popCtr 0, .pushRefCont refCellB, .popCtr 1, invertInstr, invertInstr, .pushCtr 0,
    .pushCtr 1]

private def progBlessSetC1DoubleInvertPushC1 : Array Instr :=
  #[.bless, .popCtr 1, invertInstr, invertInstr, .pushCtr 1]

private def progBlessSetC0DoubleInvertPushC0 : Array Instr :=
  #[.bless, .popCtr 0, invertInstr, invertInstr, .pushCtr 0]

private def progTripleInvertTailPush : Array Instr :=
  #[invertInstr, invertInstr, invertInstr, .pushInt (.num 8)]

private def progInvertThenAtexit : Array Instr :=
  #[invertInstr, .contExt .atexit]

private def progInvertThenBoolAnd : Array Instr :=
  #[invertInstr, .boolAnd]

private def progInvertThenPop : Array Instr :=
  #[invertInstr, .pop 0]

private def oracleCases : Array OracleCase := #[
  -- Basic success: stack must be untouched.
  mkCase "ok/basic/empty-stack" #[],
  mkCase "ok/basic/int-below" #[intV 7],
  mkCase "ok/basic/null-below" #[.null],
  mkCase "ok/basic/cell-below" #[.cell refCellA],
  mkCase "ok/basic/slice-below" #[.slice sliceA],
  mkCase "ok/basic/builder-empty-below" #[.builder Builder.empty],
  mkCase "ok/basic/tuple-empty-below" #[.tuple #[]],
  mkCase "ok/basic/cont-q0-below" #[q0V],
  mkCase "ok/basic/mixed-a" #[intV 7, .null, .cell refCellA],
  mkCase "ok/basic/mixed-b" #[.slice sliceB, .builder Builder.empty, .tuple #[], q0V],

  -- Control-flow continuation: INVERT itself has no jump.
  mkCase "ok/program/tail-nop-chain" #[intV 9] #[invertInstr, .nop, .nop],
  mkCase "ok/program/tail-pushint" #[.null] #[invertInstr, .pushInt (.num 77)],
  mkCase "ok/program/tail-add" #[intV 4] #[invertInstr, .pushInt (.num 2), .add],
  mkCase "ok/program/double-invert-tail-push" #[] #[invertInstr, invertInstr, .pushInt (.num 5)],

  -- Swap observability via follow-up ctr reads/writes.
  mkCase "ok/observe/bless-set-c1-invert-pushc0" #[.slice sliceA] progBlessSetC1InvertPushC0,
  mkCase "ok/observe/bless-set-c0-invert-pushc1" #[.slice sliceB] progBlessSetC0InvertPushC1,
  mkCase "ok/observe/bless-set-c1-double-invert-pushc1" #[.slice sliceA] progBlessSetC1DoubleInvertPushC1,
  mkCase "ok/observe/bless-set-c0-double-invert-pushc0" #[.slice sliceB] progBlessSetC0DoubleInvertPushC0,
  mkCase "ok/observe/envelope-to-c1-invert-pushc0" #[] progBuildEnvelopeToC1InvertPushC0,
  mkCase "ok/observe/envelope-to-c0-invert-pushc1" #[] progBuildEnvelopeToC0InvertPushC1,
  mkCase "ok/observe/envelope-to-c1-double-invert-pushc1" #[] progBuildEnvelopeToC1DoubleInvertPushC1,
  mkCase "ok/program/triple-invert-tail-push" #[] progTripleInvertTailPush,
  mkCase "ok/observe/invert-then-pushctr0-default" #[] #[invertInstr, .pushCtr 0],
  mkCase "ok/observe/invert-then-pushctr1-default" #[] #[invertInstr, .pushCtr 1],

  -- Downstream failures must come from following instructions, not from INVERT.
  mkCase "err/tail/atexit-underflow-after-invert" #[] progInvertThenAtexit,
  mkCase "err/tail/atexit-type-after-invert" #[intV 1] progInvertThenAtexit,
  mkCase "err/tail/booland-underflow-after-invert" #[q0V] progInvertThenBoolAnd,
  mkCase "err/tail/pop-underflow-after-invert" #[] progInvertThenPop,
  mkCase "err/tail/add-underflow-after-invert" #[] #[invertInstr, .add],

  -- Decode boundaries around 0xedf8.
  mkCodeCase "ok/decode/raw-opcode-edf8" #[intV 1] invertRawCode,
  mkCodeCase "err/decode/truncated-8" #[] invertTruncated8Code,
  mkCodeCase "err/decode/truncated-15" #[q0V] invertTruncated15Code
]

def suite : InstrSuite where
  id := invertId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/non-contExt"
          (runInvertDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/other-contExt"
          (runInvertDispatchFallback (.contExt .condSel) #[q0V])
          #[q0V, intV dispatchSentinel]
        expectOkStack "dispatch/match"
          (runInvertDispatchFallback invertInstr #[intV 1, .null])
          #[intV 1, .null] }
    ,
    { name := "unit/raw/swap-c0-c1-only"
      run := do
        let stack0 : Array Value := #[intV 44, .null, .cell refCellA]
        let c2Init : Continuation := .quit 22
        let c3Init : Continuation := .quit 33
        let st <- expectRawOk "raw/swap-c0-c1-only"
          (runInvertRaw stack0 q7 q9 c2Init c3Init ordContA)
        if st.stack != stack0 then
          throw (IO.userError s!"raw/swap-c0-c1-only: stack changed {reprStr st.stack}")
        else if st.regs.c0 != q9 then
          throw (IO.userError s!"raw/swap-c0-c1-only: expected c0=quit9, got {reprStr st.regs.c0}")
        else if st.regs.c1 != q7 then
          throw (IO.userError s!"raw/swap-c0-c1-only: expected c1=quit7, got {reprStr st.regs.c1}")
        else if st.regs.c2 != c2Init then
          throw (IO.userError s!"raw/swap-c0-c1-only: c2 changed to {reprStr st.regs.c2}")
        else if st.regs.c3 != c3Init then
          throw (IO.userError s!"raw/swap-c0-c1-only: c3 changed to {reprStr st.regs.c3}")
        else if st.cc != ordContA then
          throw (IO.userError s!"raw/swap-c0-c1-only: cc changed to {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/raw/swaps-complex-continuations-and-double-invert-identity"
      run := do
        let st1 <- expectRawOk "raw/swap-complex"
          (runInvertRaw #[.builder Builder.empty] ordContA envContB)
        if st1.stack != #[.builder Builder.empty] then
          throw (IO.userError s!"raw/swap-complex: stack changed {reprStr st1.stack}")
        else if st1.regs.c0 != envContB then
          throw (IO.userError s!"raw/swap-complex: expected c0=envContB, got {reprStr st1.regs.c0}")
        else if st1.regs.c1 != ordContA then
          throw (IO.userError s!"raw/swap-complex: expected c1=ordContA, got {reprStr st1.regs.c1}")
        let (res2, st2) := (execInstrContAtExit invertInstr (pure ())).run st1
        match res2 with
        | .error e =>
            throw (IO.userError s!"raw/double-invert: expected success, got {e}")
        | .ok _ =>
            if st2.regs.c0 != ordContA then
              throw (IO.userError s!"raw/double-invert: expected c0 restored, got {reprStr st2.regs.c0}")
            else if st2.regs.c1 != envContB then
              throw (IO.userError s!"raw/double-invert: expected c1 restored, got {reprStr st2.regs.c1}")
            else
              pure () }
    ,
    { name := "unit/direct/no-stack-type-or-underflow-checks"
      run := do
        let probes : Array (Array Value) := #[
          #[],
          #[.null],
          #[intV 0],
          #[.int .nan],
          #[.cell refCellA],
          #[.slice sliceA],
          #[.builder Builder.empty],
          #[.tuple #[]],
          #[q0V],
          #[intV 7, .null, .cell refCellB, .tuple #[]]
        ]
        for i in [0:probes.size] do
          let stack := probes[i]!
          expectOkStack s!"direct/no-stack-checks-{i}" (runInvertDirect stack) stack }
    ,
    { name := "unit/decode/invert-and-truncated-prefix"
      run := do
        expectDecodeInvert "decode/invert" invertRawCode
        expectDecodeErr "decode/truncated-8" invertTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" invertTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec invertId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.INVERT
