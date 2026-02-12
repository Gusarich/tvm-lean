import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index
import TvmLean.Native

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.AGAINENDBRK

/-!
AGAINENDBRK branch map (Lean + C++ reference):
- C++ `exec_again_end(st, true)`:
  1) `c1_save_set()`
  2) `body := extract_cc(0)`
  3) `again(body)`
- Lean `.againEnd true` should do the same ordered sequence.
- Runtime loop behavior is in `AgainCont::jump[_w]` / `.againBody`:
  - if `body.hasC0`, jump body directly;
  - otherwise set `c0 := again(body)` and jump body.
-/

private def againEndBrkId : InstrId := { name := "AGAINENDBRK" }

private def againEndBrkInstr : Instr := .contExt (.againEnd true)

private def dispatchSentinel : Int := 61733

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceB : Slice := Slice.ofCell cellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def bodyHasC0 : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0)
    { OrdCregs.empty with c0 := some (.quit 31337) }
    OrdCdata.empty

private def cregsEmpty (cregs : OrdCregs) : Bool :=
  cregs.c0.isNone &&
  cregs.c1.isNone &&
  cregs.c2.isNone &&
  cregs.c3.isNone &&
  cregs.c4.isNone &&
  cregs.c5.isNone &&
  cregs.c7.isNone

private def cdataEmpty (cdata : OrdCdata) : Bool :=
  cdata.stack.isEmpty && cdata.nargs = -1

private def runLoopExtFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowLoopExt instr (VM.push (intV dispatchSentinel)) stack

private def runAgainEndRaw
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowLoopExt againEndBrkInstr (pure ())).run st0

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

private def runAgainBodyStep
    (stack : Array Value)
    (body : Continuation)
    (c0 : Continuation := .quit 0) : StepResult :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := { Regs.initial with c0 := c0 }
      cc := .againBody body }
  VmState.step stubHost st0

private def expectContinue (label : String) (res : StepResult) : IO VmState := do
  match res with
  | .continue st => pure st
  | .halt code st =>
      throw (IO.userError s!"{label}: expected continue, got halt({code}) with state {reprStr st}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[againEndBrkInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := againEndBrkId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseWithCregs
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (initCregs : OracleInitCregs)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := againEndBrkId
    program := program
    initStack := stack
    initCregs := initCregs
    fuel := fuel }

private def progRetAlt : Array Instr :=
  #[againEndBrkInstr, .retAlt]

private def progRet : Array Instr :=
  #[againEndBrkInstr, .ret]

private def progPushRetAlt (n : Int) : Array Instr :=
  #[againEndBrkInstr, .pushInt (.num n), .retAlt]

private def progPushRet (n : Int) : Array Instr :=
  #[againEndBrkInstr, .pushInt (.num n), .ret]

private def progAddRetAlt (a b : Int) : Array Instr :=
  #[againEndBrkInstr, .pushInt (.num a), .pushInt (.num b), .add, .retAlt]

private def progAddRet (a b : Int) : Array Instr :=
  #[againEndBrkInstr, .pushInt (.num a), .pushInt (.num b), .add, .ret]

private def progAddOnly : Array Instr :=
  #[againEndBrkInstr, .add]

private def progPopCtr0 : Array Instr :=
  #[againEndBrkInstr, .popCtr 0]

private def progSetC0FromC1ImplicitRet : Array Instr :=
  #[againEndBrkInstr, .pushCtr 1, .popCtr 0]

private def progSetC0FromC1Ret : Array Instr :=
  #[againEndBrkInstr, .pushCtr 1, .popCtr 0, .ret]

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

private def againEndBrkSetGasExact : Int :=
  computeExactGasBudget againEndBrkInstr

private def againEndBrkSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne againEndBrkInstr

private def pickNoise (rng0 : StdGen) : Array Value × StdGen :=
  let (choice, rng1) := randNat rng0 0 2
  match choice with
  | 0 => (#[], rng1)
  | 1 => (noiseA, rng1)
  | _ => (noiseB, rng1)

private def pickProgramOk (rng0 : StdGen) : Array Instr × StdGen :=
  let (choice, rng1) := randNat rng0 0 5
  match choice with
  | 0 => (progRetAlt, rng1)
  | 1 => (progRet, rng1)
  | 2 =>
      let (x, rng2) := pickSigned257ish rng1
      (progPushRetAlt x, rng2)
  | 3 =>
      let (x, rng2) := pickSigned257ish rng1
      (progPushRet x, rng2)
  | 4 =>
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      (progAddRetAlt a b, rng3)
  | _ =>
      let (a, rng2) := pickSigned257ish rng1
      let (b, rng3) := pickSigned257ish rng2
      (progAddRet a b, rng3)

private def genAgainEndBrkFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  match shape with
  | 0 =>
      let (noise, rng2) := pickNoise rng1
      let (program, rng3) := pickProgramOk rng2
      (mkCase "fuzz/ok/brk" noise program, rng3)
  | 1 =>
      (mkCase "fuzz/err/brk/add-underflow" #[] progAddOnly, rng1)
  | 2 =>
      (mkCase "fuzz/err/brk/add-type" #[.null, intV 1] progAddOnly, rng1)
  | 3 =>
      (mkCase "fuzz/err/brk/popctr" #[] progPopCtr0, rng1)
  | 4 =>
      let (useExact, rng2) := randBool rng1
      let gas := if useExact then againEndBrkSetGasExact else againEndBrkSetGasExactMinusOne
      let name := if useExact then "fuzz/gas/exact" else "fuzz/gas/minus-one"
      let program := #[.pushInt (.num gas), .tonEnvOp .setGasLimit, againEndBrkInstr]
      (mkCase name #[] program, rng2)
  | _ =>
      let (noise, rng2) := pickNoise rng1
      let (program, rng3) := pickProgramOk rng2
      (mkCase "fuzz/ok/brk/noise" noise program, rng3)

def suite : InstrSuite where
  id := againEndBrkId
  unit := #[
    { name := "unit/dispatch/match-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runLoopExtFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-againendbrk"
          (runLoopExtFallback againEndBrkInstr #[.null, intV 7])
          #[.null, intV 7] }
    ,
    { name := "unit/error/nonordinary-cc-brk-saves-before-typechk"
      run := do
        let st ← expectRawErr "nonordinary/brk"
          (runAgainEndRaw #[intV 11] (.quit 7) (.quit 5) (.quit 6))
          .typeChk
        if st.stack != #[intV 11] then
          throw (IO.userError s!"nonordinary/brk: stack mismatch {reprStr st.stack}")
        else if st.regs.c1 != st.regs.c0 then
          throw (IO.userError "nonordinary/brk: expected c1 == c0 after c1SaveSet")
        else
          match st.regs.c0 with
          | .envelope ext cregs cdata =>
              if ext != .quit 5 then
                throw (IO.userError s!"nonordinary/brk: envelope ext mismatch {reprStr ext}")
              else if cregs.c1 != some (.quit 6) then
                throw (IO.userError
                  s!"nonordinary/brk: expected captured c1=quit6, got {reprStr cregs.c1}")
              else if cregs.c0.isSome then
                throw (IO.userError
                  s!"nonordinary/brk: expected no captured c0 in save-list, got {reprStr cregs.c0}")
              else if !(cdataEmpty cdata) then
                throw (IO.userError s!"nonordinary/brk: expected empty cdata, got {reprStr cdata}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"nonordinary/brk: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/brk/success-c1-save-shape-and-extracted-body"
      run := do
        let bodyCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
        let bodySlice : Slice := Slice.ofCell bodyCell
        let weirdCc : Continuation :=
          .ordinary bodySlice (.quit 77)
            { OrdCregs.empty with c0 := some (.quit 66), c1 := some (.quit 88) }
            { stack := #[intV 3], nargs := 2 }

        let st ← expectRawOk "brk/success"
          (runAgainEndRaw #[.null] weirdCc (.quit 5) (.quit 6))
        if st.stack != #[.null] then
          throw (IO.userError s!"brk/success: stack mismatch {reprStr st.stack}")
        else if st.regs.c1 != st.regs.c0 then
          throw (IO.userError "brk/success: expected c1 == c0 after c1SaveSet")
        else
          match st.regs.c0 with
          | .envelope ext cregs _ =>
              if ext != .quit 5 then
                throw (IO.userError s!"brk/success: envelope ext mismatch {reprStr ext}")
              else if cregs.c1 != some (.quit 6) then
                throw (IO.userError s!"brk/success: expected captured c1=quit6, got {reprStr cregs.c1}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"brk/success: expected envelope c0, got {reprStr other}")
        match st.cc with
        | .againBody body =>
            match body with
            | .ordinary code saved cregs cdata =>
                if code != bodySlice then
                  throw (IO.userError s!"brk/success: extracted code mismatch {reprStr code}")
                else if saved != .quit 0 then
                  throw (IO.userError s!"brk/success: expected extracted saved=quit0, got {reprStr saved}")
                else if !(cregsEmpty cregs) then
                  throw (IO.userError s!"brk/success: expected empty body cregs, got {reprStr cregs}")
                else if !(cdataEmpty cdata) then
                  throw (IO.userError s!"brk/success: expected empty body cdata, got {reprStr cdata}")
                else
                  pure ()
            | other =>
                throw (IO.userError s!"brk/success: expected ordinary extracted body, got {reprStr other}")
        | other =>
            throw (IO.userError s!"brk/success: expected againBody cc, got {reprStr other}") }
    ,
    { name := "unit/runtime/againbody-no-c0-installs-self"
      run := do
        let body : Continuation := .quit 9
        let marker : Continuation := .quit 44
        let st ← expectContinue "runtime/no-c0"
          (runAgainBodyStep #[intV 7] body marker)
        if st.stack != #[intV 7] then
          throw (IO.userError s!"runtime/no-c0: stack mismatch {reprStr st.stack}")
        else if st.cc != body then
          throw (IO.userError s!"runtime/no-c0: expected cc=body, got {reprStr st.cc}")
        else if st.regs.c0 != .againBody body then
          throw (IO.userError
            s!"runtime/no-c0: expected c0=againBody(body), got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/runtime/againbody-has-c0-keeps-c0"
      run := do
        let marker : Continuation := .quit 45
        let st ← expectContinue "runtime/has-c0"
          (runAgainBodyStep #[intV 8] bodyHasC0 marker)
        if st.stack != #[intV 8] then
          throw (IO.userError s!"runtime/has-c0: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != marker then
          throw (IO.userError
            s!"runtime/has-c0: expected c0 unchanged={reprStr marker}, got {reprStr st.regs.c0}")
        else
          match st.cc with
          | .ordinary _ _ cregs _ =>
              if cregs.c0 != some (.quit 31337) then
                throw (IO.userError
                  s!"runtime/has-c0: expected body c0 marker 31337, got {reprStr cregs.c0}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"runtime/has-c0: expected ordinary body cc, got {reprStr other}") }
  ]
  oracle := #[
    -- Successful terminating bodies.
    mkCase "ok/brk/retalt/empty" #[] progRetAlt,
    mkCase "ok/brk/retalt/noise-a" noiseA progRetAlt,
    mkCase "ok/brk/retalt/noise-b" noiseB progRetAlt,
    mkCase "ok/brk/ret/empty" #[] progRet,
    mkCase "ok/brk/ret/noise-a" noiseA progRet,
    mkCase "ok/brk/ret/noise-b" noiseB progRet,
    mkCase "ok/brk/push-retalt/zero" #[] (progPushRetAlt 0),
    mkCase "ok/brk/push-retalt/pos" #[] (progPushRetAlt 6),
    mkCase "ok/brk/push-retalt/neg" #[intV 3] (progPushRetAlt (-4)),
    mkCase "ok/brk/push-retalt/deep-a" #[.builder Builder.empty, intV 5] (progPushRetAlt 13),
    mkCase "ok/brk/push-retalt/deep-b" #[.cell cellA, .null, intV 1] (progPushRetAlt (-15)),
    mkCase "ok/brk/push-ret/pos" #[] (progPushRet 9),
    mkCase "ok/brk/push-ret/neg" #[intV 2] (progPushRet (-7)),
    mkCase "ok/brk/push-ret/deep" #[.slice fullSliceB, .tuple #[]] (progPushRet 22),
    mkCase "ok/brk/add-retalt/basic" #[] (progAddRetAlt 1 2),
    mkCase "ok/brk/add-retalt/mixed-sign" #[.null, intV 10] (progAddRetAlt (-2) 9),
    mkCase "ok/brk/add-retalt/deep-cell" #[.cell cellB, intV 1] (progAddRetAlt 5 (-8)),
    mkCase "ok/brk/add-retalt/zero-sum" #[.builder Builder.empty] (progAddRetAlt 100 (-100)),
    mkCase "ok/brk/add-ret/basic" #[] (progAddRet 3 4),
    mkCase "ok/brk/add-ret/mixed-sign" #[.null, intV 11] (progAddRet (-6) 10),
    mkCase "ok/brk/add-ret/deep-slice" #[.slice fullSliceB, intV 9] (progAddRet 8 (-3)),
    mkCase "ok/brk/add-ret/zero-sum" #[.cell cellA] (progAddRet 77 (-77)),
    mkCase "ok/brk/setc0fromc1-implicitret/empty" #[] progSetC0FromC1ImplicitRet,
    mkCase "ok/brk/setc0fromc1-implicitret/noise-a" #[.cell cellA, intV 7] progSetC0FromC1ImplicitRet,
    mkCase "ok/brk/setc0fromc1-implicitret/noise-b" #[.slice fullSliceB, .tuple #[]] progSetC0FromC1ImplicitRet,
    mkCase "ok/brk/setc0fromc1-ret/empty" #[] progSetC0FromC1Ret,
    mkCase "ok/brk/setc0fromc1-ret/noise-a" #[.cell cellA, intV 7] progSetC0FromC1Ret,
    mkCase "ok/brk/setc0fromc1-ret/noise-b" #[.slice fullSliceB, .tuple #[]] progSetC0FromC1Ret,
    mkCase "ok/brk/retalt/trailing-skipped" #[] #[againEndBrkInstr, .retAlt, .pushInt (.num 777)],
    mkCase "ok/brk/push-retalt/trailing-skipped" #[] #[againEndBrkInstr, .pushInt (.num 4), .retAlt, .pushInt (.num 8)],
    mkCase "ok/brk/ret/trailing-skipped" #[] #[againEndBrkInstr, .ret, .pushInt (.num 999)],
    mkCase "ok/brk/setc0fromc1-ret/trailing-skipped" #[] #[againEndBrkInstr, .pushCtr 1, .popCtr 0, .ret, .pushInt (.num 314)],
    mkCase "ok/brk/add-ret/trailing-skipped" #[] #[againEndBrkInstr, .pushInt (.num 1), .pushInt (.num 2), .add, .ret, .pushInt (.num 9)],

    -- Deterministic body errors.
    mkCase "err/brk/body-add-underflow-empty" #[] progAddOnly,
    mkCase "err/brk/body-add-underflow-one" #[intV 1] progAddOnly,
    mkCase "err/brk/body-add-type" #[.null, intV 1] progAddOnly,
    mkCase "err/brk/body-add-type-deep" #[.cell cellA, .null, intV 1] progAddOnly,
    mkCase "err/brk/body-popctr-underflow" #[] progPopCtr0,
    mkCase "err/brk/body-popctr-type" #[.null] progPopCtr0,
    mkCase "err/brk/body-popctr-type-deep" #[.slice fullSliceB, intV 3] progPopCtr0
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr againEndBrkId
      count := 500
      gen := genAgainEndBrkFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.AGAINENDBRK
