import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BOOLOR

/-
BOOLOR branch map (Lean vs C++):
- Lean audited:
  - `TvmLean/Semantics/Exec/Cont/BoolOr.lean`
  - `TvmLean/Model/Cont/Continuation.lean` (`forceCdata`, `defineC1`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`pop`, `popCont`)
- C++ audited:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_compos(mask=2)`)
  - `/Users/daniil/Coding/ton/crypto/vm/continuation.h` (`ControlRegs::define_c1`)

Coverage goals:
1. dispatch branch (`.boolOr` vs fallback);
2. error ordering parity:
  - `check_underflow(2)` before any `pop_cont` type checks;
  - top (`val`) popped/type-checked before second (`cont`);
3. `force_cregs` parity for continuations without cdata;
4. `define_c1` semantics (set if absent, preserve if already defined);
5. decode boundaries for opcode `0xedf1`.
-/

private def boolOrId : InstrId := { name := "BOOLOR" }
private def boolOrInstr : Instr := .boolOr

private def dispatchSentinel : Int := 51823

private def q0 : Value := .cont (.quit 0)
private def q1 : Value := .cont (.quit 1)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def mkStack (below : Array Value) (cont : Value := q0) (val : Value := q0) : Array Value :=
  below ++ #[cont, val]

private def runDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContBoolOr boolOrInstr stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContBoolOr instr (VM.push (intV dispatchSentinel)) stack

private def runRaw (stack : Array Value) (instr : Instr := boolOrInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContBoolOr instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
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

private def expectDecodeBoolOr
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .boolOr then
        throw (IO.userError s!"{label}: expected .boolOr, got {reprStr instr}")
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
    (program : Array Instr := #[boolOrInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := boolOrId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := boolOrId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def boolOrCode : Cell :=
  Cell.mkOrdinary (natToBits 0xedf1 16) #[]

private def boolOrTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def boolOrTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xedf1 >>> 1) 15) #[]

private def progPushCtr1BoolOr : Array Instr :=
  #[.pushCtr 1, boolOrInstr]

private def progSwapWithCtr1BoolOr : Array Instr :=
  #[.pushCtr 1, .xchg0 1, boolOrInstr]

private def progC0C1BoolOr : Array Instr :=
  #[.pushCtr 0, .pushCtr 1, boolOrInstr]

private def progBoolOrTailPush : Array Instr :=
  #[boolOrInstr, .pushInt (.num 77)]

private def progDoubleBoolOr : Array Instr :=
  #[boolOrInstr, boolOrInstr]

private def progBoolOrPopCtr1PushCtr1 : Array Instr :=
  #[boolOrInstr, .popCtr 1, .pushCtr 1]

private def progPushNanBoolOr : Array Instr :=
  #[.pushInt .nan, boolOrInstr]

private def oracleCases : Array OracleCase := #[
  -- Success / continuation branch coverage.
  mkCase "ok/basic/q0-q0-empty" (mkStack #[]),
  mkCase "ok/basic/q0-q0-below-int" (mkStack #[intV 7]),
  mkCase "ok/basic/q0-q0-below-mixed-a" (mkStack #[.null, .cell cellA]),
  mkCase "ok/basic/q0-q0-below-mixed-b" (mkStack #[.builder Builder.empty, .tuple #[]]),
  mkCase "ok/basic/q0-q0-below-slice" (mkStack #[.slice sliceA]),
  mkCase "ok/order/tail-continues-push" (mkStack #[intV 3]) progBoolOrTailPush,
  mkCase "ok/order/program-pushctr1-as-val" #[q0] progPushCtr1BoolOr,
  mkCase "ok/order/program-pushctr1-as-cont" #[q0] progSwapWithCtr1BoolOr,
  mkCase "ok/order/program-c0-c1-no-init" #[] progC0C1BoolOr,
  mkCase "ok/order/program-double-boolor" #[q0, q0, q0] progDoubleBoolOr,
  mkCase "ok/order/program-popctr1-pushctr1" (mkStack #[intV 9]) progBoolOrPopCtr1PushCtr1,
  mkCodeCase "ok/decode/raw-exact-edf1" (mkStack #[intV 1]) boolOrCode,

  -- Underflow parity (`check_underflow(2)` before type checks).
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/single-q0" #[q0],
  mkCase "err/underflow/single-null" #[.null],
  mkCase "err/underflow/single-int" #[intV 1],
  mkCase "err/underflow/single-cell" #[.cell cellA],
  mkCase "err/underflow/single-slice" #[.slice sliceA],
  mkCase "err/underflow/single-builder" #[.builder Builder.empty],
  mkCase "err/underflow/single-tuple" #[.tuple #[]],

  -- Type checks: top (`val`) popped first.
  mkCase "err/type/top-null" (mkStack #[] q0 .null),
  mkCase "err/type/top-int" (mkStack #[] q0 (intV 1)),
  mkCase "err/type/top-cell" (mkStack #[] q0 (.cell cellA)),
  mkCase "err/type/top-slice" (mkStack #[] q0 (.slice sliceA)),
  mkCase "err/type/top-builder" (mkStack #[] q0 (.builder Builder.empty)),
  mkCase "err/type/top-tuple" (mkStack #[] q0 (.tuple #[])),
  mkCase "err/type/top-both-noncont-pop-top-first" (mkStack #[] .null (.cell cellB)),
  mkCase "err/type/top-nan-via-program" #[q0] progPushNanBoolOr,

  -- Type checks: second (`cont`) after top continuation succeeds.
  mkCase "err/type/second-null" (mkStack #[] .null q0),
  mkCase "err/type/second-int" (mkStack #[] (intV 1) q0),
  mkCase "err/type/second-cell" (mkStack #[] (.cell cellB) q0),
  mkCase "err/type/second-slice" (mkStack #[] (.slice sliceB) q0),
  mkCase "err/type/second-builder" (mkStack #[] (.builder Builder.empty) q0),
  mkCase "err/type/second-tuple" (mkStack #[] (.tuple #[]) q0),

  -- Explicit ordering probes.
  mkCase "order/underflow-before-top-type-program-one-item"
    #[]
    #[.pushInt (.num 1), boolOrInstr],
  mkCase "order/top-type-before-second-type"
    (mkStack #[] .null (.cell cellA)),
  mkCase "order/second-type-after-top-cont"
    (mkStack #[] (.cell cellA) q0),

  -- Decode failures around `0xedf1` width.
  mkCodeCase "err/decode/truncated-8-prefix" #[] boolOrTruncated8Code,
  mkCodeCase "err/decode/truncated-15-prefix" #[q0, q0] boolOrTruncated15Code
]

def suite : InstrSuite where
  id := boolOrId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback"
          (runFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectErr "dispatch/match-no-next"
          (runFallback boolOrInstr #[.null])
          .stkUnd }
    ,
    { name := "unit/error-order/underflow-before-type-single-noncont"
      run :=
        expectErr "underflow-before-type-single-noncont"
          (runDirect #[.null])
          .stkUnd }
    ,
    { name := "unit/error-order/top-before-second-type"
      run :=
        expectErr "top-before-second-type"
          (runDirect (mkStack #[] .null (.cell cellA)))
          .typeChk }
    ,
    { name := "unit/error-order/second-after-top-cont"
      run :=
        expectErr "second-after-top-cont"
          (runDirect (mkStack #[] (.cell cellA) q0))
          .typeChk }
    ,
    { name := "unit/raw/force-cdata-wraps-noncdata-cont"
      run := do
        let st ← expectRawOk "force-cdata-wraps-noncdata-cont"
          (runRaw (mkStack #[] q1 q0))
        match st.stack with
        | #[.cont (.envelope ext cregs cdata)] =>
            if ext != .quit 1 then
              throw (IO.userError
                s!"force-cdata-wraps-noncdata-cont: expected ext=quit1, got {reprStr ext}")
            else if cregs.c1 != some (.quit 0) then
              throw (IO.userError
                s!"force-cdata-wraps-noncdata-cont: expected c1=quit0, got {reprStr cregs.c1}")
            else if cregs.c0.isSome || cregs.c2.isSome || cregs.c3.isSome
                || cregs.c4.isSome || cregs.c5.isSome || cregs.c7.isSome then
              throw (IO.userError
                s!"force-cdata-wraps-noncdata-cont: unexpected cregs payload {reprStr cregs}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError
                s!"force-cdata-wraps-noncdata-cont: unexpected cdata {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"force-cdata-wraps-noncdata-cont: unexpected final stack {reprStr st.stack}") }
    ,
    { name := "unit/raw/define-c1-preserves-existing"
      run := do
        let cregs0 : OrdCregs := { OrdCregs.empty with c1 := some (.quit 9) }
        let cont : Value := .cont (.ordinary sliceA (.quit 0) cregs0 OrdCdata.empty)
        let st ← expectRawOk "define-c1-preserves-existing"
          (runRaw (mkStack #[] cont q0))
        match st.stack with
        | #[.cont (.ordinary code saved cregs cdata)] =>
            if code != sliceA then
              throw (IO.userError
                s!"define-c1-preserves-existing: code mismatch {reprStr code}")
            else if saved != .quit 0 then
              throw (IO.userError
                s!"define-c1-preserves-existing: saved mismatch {reprStr saved}")
            else if cregs.c1 != some (.quit 9) then
              throw (IO.userError
                s!"define-c1-preserves-existing: expected c1=quit9, got {reprStr cregs.c1}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError
                s!"define-c1-preserves-existing: cdata mismatch {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"define-c1-preserves-existing: unexpected final stack {reprStr st.stack}") }
    ,
    { name := "unit/raw/define-c1-sets-when-empty"
      run := do
        let cregs0 : OrdCregs := { OrdCregs.empty with c0 := some (.quit 7) }
        let cont : Value := .cont (.ordinary sliceB (.quit 0) cregs0 OrdCdata.empty)
        let st ← expectRawOk "define-c1-sets-when-empty"
          (runRaw (mkStack #[] cont q1))
        match st.stack with
        | #[.cont (.ordinary code saved cregs cdata)] =>
            if code != sliceB then
              throw (IO.userError
                s!"define-c1-sets-when-empty: code mismatch {reprStr code}")
            else if saved != .quit 0 then
              throw (IO.userError
                s!"define-c1-sets-when-empty: saved mismatch {reprStr saved}")
            else if cregs.c0 != some (.quit 7) then
              throw (IO.userError
                s!"define-c1-sets-when-empty: expected c0=quit7, got {reprStr cregs.c0}")
            else if cregs.c1 != some (.quit 1) then
              throw (IO.userError
                s!"define-c1-sets-when-empty: expected c1=quit1, got {reprStr cregs.c1}")
            else if cdata.stack != #[] || cdata.nargs != -1 then
              throw (IO.userError
                s!"define-c1-sets-when-empty: cdata mismatch {reprStr cdata}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"define-c1-sets-when-empty: unexpected final stack {reprStr st.stack}") }
    ,
    { name := "unit/decode/boolor-and-truncated-prefix"
      run := do
        expectDecodeBoolOr "decode/boolor" boolOrCode
        expectDecodeErr "decode/truncated-8" boolOrTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" boolOrTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec boolOrId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.BOOLOR
