import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RETVARARGS

/-
RETVARARGS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/RetVarArgs.lean` (`execInstrFlowRetVarArgs`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, integer/type behavior)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdb39 -> .retVarArgs`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.retVarArgs -> 0xdb39`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ret_varargs`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`pop_smallint_range`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret`, `VmState::jump`)

Branch map covered by this suite:
1. dispatch: `.retVarArgs` handled vs fallback to `next`.
2. pop gate:
  - underflow (`stkUnd`) on empty stack;
  - non-int top (`typeChk`);
  - out-of-range top (`rangeChk`) for `< -1` or `> 254`;
  - NaN/non-smallint path from C++ `pop_smallint_range(254, -1)` must be `rangeChk`.
3. RET path:
  - `retvals = -1` => pass whole current stack;
  - `retvals >= 0` => pass exactly top `retvals` values;
  - jump-time checks delegated to `VM.jump` (`stkUnd` for depth/nargs violations).
4. ordering:
  - `retvals` is popped before any jump-time checks, so failing jumps leave stack without that top element.
5. decode/assembly boundaries:
  - exact 16-bit opcode `0xdb39`;
  - truncated 8/15-bit prefixes must fail decode.

Mismatch found and fixed:
- Lean previously used `popIntFinite`, yielding `intOv` for NaN.
- C++ `exec_ret_varargs` uses `pop_smallint_range(254, -1)`, yielding `range_chk` for NaN/non-smallint.
- Patched Lean to map NaN to `.rangeChk` in `execInstrFlowRetVarArgs`.
-/

private def retVarArgsId : InstrId := { name := "RETVARARGS" }

private def retVarArgsInstr : Instr := .retVarArgs

private def dispatchSentinel : Int := 49079

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def fullSliceA : Slice :=
  Slice.ofCell refCellA

private def fullSliceB : Slice :=
  Slice.ofCell refCellB

private def q0 : Value := .cont (.quit 0)

private def noiseA : Array Value :=
  #[.null, intV 7, .cell refCellA]

private def noiseB : Array Value :=
  #[.slice fullSliceB, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0, intV (-4), .null]

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def c0Captured (captured : Array Value) (nargs : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := captured, nargs := nargs }

private def withRetvals (below : Array Value) (retvals : Int) : Array Value :=
  below ++ #[intV retvals]

private def mkIntRangeStack (n : Nat) : Array Value :=
  (Array.range n).map (fun i => intV (Int.ofNat i))

private def range254 : Array Value := mkIntRangeStack 254

private def range255 : Array Value := mkIntRangeStack 255

private def runRetVarArgsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowRetVarArgs retVarArgsInstr stack

private def runRetVarArgsFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRetVarArgs instr (VM.push (intV dispatchSentinel)) stack

private def runRetVarArgsRaw
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1)
    (instr : Instr := retVarArgsInstr) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrFlowRetVarArgs instr (pure ())).run st0

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

private def expectDecodeRetVarArgs
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .retVarArgs then
        throw (IO.userError s!"{label}: expected .retVarArgs, got {reprStr instr}")
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
    (program : Array Instr := #[retVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retVarArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .retVarArgs] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, .retVarArgs] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    .retVarArgs] ++ tail

private def retVarArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retVarArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb39 >>> 1) 15) #[]

def suite : InstrSuite where
  id := retVarArgsId
  unit := #[
    { name := "unit/dispatch/retvarargs-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetVarArgsFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-retvarargs"
          (runRetVarArgsFallback retVarArgsInstr #[intV 7, intV 1])
          #[intV 7] }
    ,
    { name := "unit/errors/underflow-type-range"
      run := do
        expectErr "underflow/empty" (runRetVarArgsDirect #[]) .stkUnd
        expectErr "type/top-null" (runRetVarArgsDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runRetVarArgsDirect #[.cell refCellA]) .typeChk
        expectErr "type/top-slice" (runRetVarArgsDirect #[.slice fullSliceA]) .typeChk
        expectErr "type/top-builder" (runRetVarArgsDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runRetVarArgsDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont" (runRetVarArgsDirect #[q0]) .typeChk
        expectErr "range/top-nan" (runRetVarArgsDirect #[.int .nan]) .rangeChk
        expectErr "range/too-small" (runRetVarArgsDirect #[intV (-2)]) .rangeChk
        expectErr "range/too-large" (runRetVarArgsDirect #[intV 255]) .rangeChk }
    ,
    { name := "unit/order/pop-before-jump-check"
      run := do
        let c0Need2 := c0NeedArgs 2
        let st ← expectRawErr "order/pop-before-jump-check"
          (runRetVarArgsRaw #[intV 88, intV (-1)] (mkOrdCont) c0Need2) .stkUnd
        if st.stack != #[intV 88] then
          throw (IO.userError
            s!"order/pop-before-jump-check: expected stack #[88], got {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"order/pop-before-jump-check: expected c0 reset before jump, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/ret/passargs-and-c0-reset"
      run := do
        let st ← expectRawOk "ret/passargs-and-c0-reset"
          (runRetVarArgsRaw #[intV 42, intV 1] (mkOrdCont) (.quit 9))
        if st.stack != #[intV 42] then
          throw (IO.userError s!"ret/passargs-and-c0-reset: stack mismatch {reprStr st.stack}")
        else if st.cc != .quit 9 then
          throw (IO.userError s!"ret/passargs-and-c0-reset: expected cc=quit9, got {reprStr st.cc}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError
            s!"ret/passargs-and-c0-reset: expected c0 reset to quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/ret/pass0-drops-stack"
      run := do
        let st ← expectRawOk "ret/pass0-drops-stack"
          (runRetVarArgsRaw #[.null, intV 7, intV 0] (mkOrdCont) (.quit 5))
        if !st.stack.isEmpty then
          throw (IO.userError s!"ret/pass0-drops-stack: expected empty stack, got {reprStr st.stack}")
        else if st.cc != .quit 5 then
          throw (IO.userError s!"ret/pass0-drops-stack: expected cc=quit5, got {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/ret/captured-stack-merge"
      run := do
        let c0Cap := c0Captured #[intV 100] 1
        let st ← expectRawOk "ret/captured-stack-merge"
          (runRetVarArgsRaw #[intV 7, intV 1] (mkOrdCont) c0Cap)
        if st.stack != #[intV 100, intV 7] then
          throw (IO.userError
            s!"ret/captured-stack-merge: expected #[100,7], got {reprStr st.stack}")
        else if st.cc != c0Cap then
          throw (IO.userError s!"ret/captured-stack-merge: expected jump target c0, got {reprStr st.cc}")
        else
          pure () }
    ,
    { name := "unit/decode/retvarargs-and-truncated-prefix"
      run := do
        expectDecodeRetVarArgs "decode/retvarargs" (Cell.mkOrdinary (natToBits 0xdb39 16) #[])
        expectDecodeErr "decode/truncated-8" retVarArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" retVarArgsTruncated15Code .invOpcode }
  ]
  oracle := #[
    -- Basic RET behavior with direct `retvals` bounds.
    mkCase "ok/default/pass-minus1-empty" (withRetvals #[] (-1)),
    mkCase "ok/default/pass-minus1-int" (withRetvals #[intV 5] (-1)),
    mkCase "ok/default/pass-minus1-noise-a" (withRetvals noiseA (-1)),
    mkCase "ok/default/pass-minus1-noise-b" (withRetvals noiseB (-1)),
    mkCase "ok/default/pass0-empty" (withRetvals #[] 0),
    mkCase "ok/default/pass0-noise-c" (withRetvals noiseC 0),
    mkCase "ok/default/pass1-single" (withRetvals #[intV 7] 1),
    mkCase "ok/default/pass1-drop-lower" (withRetvals #[intV 1, intV 2, intV 3] 1),
    mkCase "ok/default/pass2-exact" (withRetvals #[intV 5, intV 6] 2),
    mkCase "ok/default/pass2-drop-bottom" (withRetvals #[intV 4, intV 5, intV 6] 2),
    mkCase "ok/default/pass254-with-254-args" (withRetvals range254 254),
    mkCase "ok/default/pass254-with-255-args" (withRetvals range255 254),
    mkCase "ok/default/trailing-push-skipped" (withRetvals #[intV 7] 1)
      #[retVarArgsInstr, .pushInt (.num 777)],
    mkCase "ok/default/trailing-add-skipped" (withRetvals #[intV 2, intV 3] 1)
      #[retVarArgsInstr, .pushInt (.num 4), .pushInt (.num 5), .add],

    -- Retarget c0 to c1 (quit1), still via RETVARARGS.
    mkCase "ok/c0-from-c1/pass-minus1" (withRetvals #[] (-1)) (progSetC0FromC1),
    mkCase "ok/c0-from-c1/pass0" (withRetvals #[] 0) (progSetC0FromC1),
    mkCase "ok/c0-from-c1/pass1" (withRetvals #[intV 9] 1) (progSetC0FromC1),
    mkCase "ok/c0-from-c1/trailing-skipped" (withRetvals #[intV 9] 1)
      (progSetC0FromC1 #[.pushInt (.num 321)]),

    -- c0 nargs branch coverage (`VM.jump` checks after retvals pop).
    mkCase "ok/c0-nargs0/pass-minus1-noise" (withRetvals noiseB (-1)) (progSetC0Nargs 0),
    mkCase "ok/c0-nargs1/pass-minus1-onearg" (withRetvals #[intV 11] (-1)) (progSetC0Nargs 1),
    mkCase "err/c0-nargs1/pass-minus1-underflow-empty" (withRetvals #[] (-1)) (progSetC0Nargs 1),
    mkCase "err/c0-nargs1/pass0-nargs-greater" (withRetvals #[intV 11] 0) (progSetC0Nargs 1),
    mkCase "ok/c0-nargs2/pass-minus1-twoargs" (withRetvals #[intV 11, intV 12] (-1)) (progSetC0Nargs 2),
    mkCase "err/c0-nargs2/pop-order-underflow" (withRetvals #[intV 11] (-1)) (progSetC0Nargs 2),
    mkCase "err/c0-nargs2/pass1-too-few-passed" (withRetvals #[intV 11, intV 12] 1) (progSetC0Nargs 2),

    -- c0 closure-stack merge via SETCONTVARARGS.
    mkCase "ok/captured/more-minus1-pass-minus1" (withRetvals #[intV 9] (-1)) (progSetC0Captured 70 (-1)),
    mkCase "ok/captured/more-minus1-pass1" (withRetvals #[intV 9, intV 8] 1) (progSetC0Captured 71 (-1)),
    mkCase "ok/captured/more0-pass-minus1" (withRetvals #[intV 9] (-1)) (progSetC0Captured 72 0),
    mkCase "ok/captured/more1-pass-minus1" (withRetvals #[intV 9] (-1)) (progSetC0Captured 73 1),
    mkCase "err/captured/more2-pass-minus1-underflow" (withRetvals #[intV 9] (-1)) (progSetC0Captured 74 2),
    mkCase "ok/captured/more2-pass-minus1-twoargs" (withRetvals #[intV 9, intV 10] (-1)) (progSetC0Captured 75 2),
    mkCase "err/captured/more1-pass0-nargs-greater" (withRetvals #[intV 9] 0) (progSetC0Captured 76 1),

    -- Error branches from pop_smallint_range(254, -1) parity.
    mkCase "err/underflow-empty" #[],
    mkCase "err/type-top-null" #[.null],
    mkCase "err/type-top-cell" #[.cell refCellA],
    mkCase "err/type-top-slice" #[.slice fullSliceA],
    mkCase "err/type-top-builder" #[.builder Builder.empty],
    mkCase "err/type-top-tuple" #[.tuple #[]],
    mkCase "err/type-top-cont-quit0" #[q0],
    mkCase "err/range-too-small" #[intV (-2)],
    mkCase "err/range-too-large" #[intV 255],
    mkCase "err/range-max-int257" #[intV maxInt257],
    mkCase "err/range-min-int257" #[intV minInt257],
    mkCase "err/range-nan-via-program" #[] #[.pushInt .nan, retVarArgsInstr],

    -- Decode errors around RETVARARGS prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retVarArgsTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retVarArgsTruncated15Code
  ]
  fuzz := #[ mkReplayOracleFuzzSpec retVarArgsId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RETVARARGS
