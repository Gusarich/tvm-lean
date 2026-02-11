import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cont.RETARGS

/-
RETARGS branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Flow/RetArgs.lean` (`execInstrFlowRetArgs`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.ret`, `VM.jump`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xdb2_ -> .retArgs`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`.retArgs n -> 0xdb20 + n`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp` (`exec_ret_args`)
  - `/Users/daniil/Coding/ton/crypto/vm/vm.cpp` (`VmState::ret`, `VmState::jump`, `adjust_jump_cont`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp` (`move_from_stack`, underflow/type guards)

Covered branches in this suite:
1. dispatch/fallback and cp0 decode boundaries for 12+4 opcode shape;
2. RETARGS core (`ret(n)`): c0 reset before jump-time checks;
3. jump-time ordering: `pass_args` underflow before closure `nargs` checks;
4. return-path shaping with closure stack and fixed/var nargs;
5. caller-continuation interaction via real `CALLXARGS` frames returning through RETARGS.

Mismatch fixed in this worker:
- C++ helper canonicalizes raw helper args as `args & 15` before `ret(params)`.
- Lean previously passed arbitrary AST `n` directly.
- `execInstrFlowRetArgs` now canonicalizes with `n &&& 0xf` for helper parity.
-/

private def retArgsId : InstrId := { name := "RETARGS" }

private def dispatchSentinel : Int := 49095

private def q0 : Value := .cont (.quit 0)

private def defaultCc : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty OrdCdata.empty

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def fullSliceA : Slice :=
  Slice.ofCell cellA

private def noiseA : Array Value :=
  #[.null, intV 7, .cell cellA]

private def noiseB : Array Value :=
  #[.slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def noiseC : Array Value :=
  #[q0, .cell cellB, .null, intV (-4)]

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def c0Captured (captured : Array Value) (nargs : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := captured, nargs := nargs }

private def retArgsInstr (n : Nat) : Instr :=
  .retArgs n

private def mkIntRangeStack (n : Nat) : Array Value :=
  (Array.range n).map (fun i => intV (Int.ofNat i))

private def range14 : Array Value :=
  mkIntRangeStack 14

private def range15 : Array Value :=
  mkIntRangeStack 15

private def range16 : Array Value :=
  mkIntRangeStack 16

private def runRetArgsDirect (n : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowRetArgs (retArgsInstr n) stack

private def runRetArgsFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowRetArgs instr (VM.push (intV dispatchSentinel)) stack

private def runRetArgsRaw
    (instr : Instr)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      regs := regs
      cc := cc }
  (execInstrFlowRetArgs instr (pure ())).run st0

private def runRetArgsRawN
    (n : Nat)
    (stack : Array Value)
    (regs : Regs := Regs.initial)
    (cc : Continuation := defaultCc) : Except Excno Unit × VmState :=
  runRetArgsRaw (retArgsInstr n) stack regs cc

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

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
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr}/{bits}")

private def expectDecodeRetArgs
    (label : String)
    (code : Cell)
    (expectedParams : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .retArgs expectedParams then
        throw (IO.userError s!"{label}: expected .retArgs {expectedParams}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def mkContSlice! (label : String) (program : Array Instr) : Slice :=
  Slice.ofCell (assembleNoRefCell! label program)

private def progCallxRetArgs
    (calleeRet : Nat)
    (params : Nat)
    (retVals : Int)
    (tail : Array Instr := #[]) : Array Instr :=
  let callee : Slice := mkContSlice! s!"retargs/callee/{calleeRet}" #[.retArgs calleeRet]
  #[.pushCont callee, .callxArgs params retVals] ++ tail

private def progSetC0FromC1 (params : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .retArgs params] ++ tail

private def progSetC0Nargs (nargs : Int) (params : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num nargs), .setNumVarArgs, .popCtr 0, .retArgs params] ++ tail

private def progSetC0Captured
    (capture : Int)
    (more : Int)
    (params : Nat)
    (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    .retArgs params] ++ tail

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := retArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def retArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def retArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb20 >>> 1) 15) #[]

private def oracleCases : Array OracleCase :=
  #[
    -- Basic RETARGS with default c0=quit0.
    mkCase "ok/default/pass0-empty" #[] #[retArgsInstr 0],
    mkCase "ok/default/pass0-drop-all-noise" noiseA #[retArgsInstr 0],
    mkCase "ok/default/pass1-single" #[intV 7] #[retArgsInstr 1],
    mkCase "ok/default/pass1-drop-lower" #[intV 1, intV 2, intV 3] #[retArgsInstr 1],
    mkCase "ok/default/pass2-exact" #[intV 5, intV 6] #[retArgsInstr 2],
    mkCase "ok/default/pass2-drop-bottom" #[intV 4, intV 5, intV 6] #[retArgsInstr 2],
    mkCase "ok/default/pass15-exact" range15 #[retArgsInstr 15],
    mkCase "ok/default/pass15-drop-bottom16" range16 #[retArgsInstr 15],
    mkCase "err/default/pass1-underflow-empty" #[] #[retArgsInstr 1],
    mkCase "err/default/pass2-underflow-one" #[intV 9] #[retArgsInstr 2],
    mkCase "err/default/pass15-underflow14" range14 #[retArgsInstr 15],
    mkCase "ok/default/noise-pass1" noiseB #[retArgsInstr 1],
    mkCase "ok/default/noise-pass2" noiseC #[retArgsInstr 2],
    mkCase "ok/default/trailing-push-skipped" #[intV 9] #[retArgsInstr 1, .pushInt (.num 777)],
    mkCase "ok/default/trailing-add-skipped" #[intV 2, intV 3] #[retArgsInstr 1, .add],

    -- Retarget c0 to c1 (quit1), still via RETARGS.
    mkCase "ok/c0-from-c1/pass0" #[] (progSetC0FromC1 0),
    mkCase "ok/c0-from-c1/pass1" #[intV 12] (progSetC0FromC1 1),
    mkCase "ok/c0-from-c1/pass2" #[intV 5, intV 6] (progSetC0FromC1 2),
    mkCase "err/c0-from-c1/pass2-underflow-one" #[intV 5] (progSetC0FromC1 2),
    mkCase "ok/c0-from-c1/trailing-skipped" #[intV 8] (progSetC0FromC1 1 #[.pushInt (.num 999)]),

    -- c0 nargs branch coverage via SETNUMVARARGS.
    mkCase "ok/nargs0/pass0-empty" #[] (progSetC0Nargs 0 0),
    mkCase "ok/nargs0/pass2-twoargs" #[intV 8, intV 9] (progSetC0Nargs 0 2),
    mkCase "err/nargs1/pass0-nargs-greater" #[intV 11] (progSetC0Nargs 1 0),
    mkCase "ok/nargs1/pass1" #[intV 11] (progSetC0Nargs 1 1),
    mkCase "err/nargs2/pass1-nargs-greater" #[intV 11, intV 12] (progSetC0Nargs 2 1),
    mkCase "ok/nargs2/pass2" #[intV 11, intV 12] (progSetC0Nargs 2 2),
    mkCase "err/nargs2/pass3-passargs-underflow" #[intV 11, intV 12] (progSetC0Nargs 2 3),
    mkCase "ok/nargs2/pass3-threeargs" #[intV 11, intV 12, intV 13] (progSetC0Nargs 2 3),
    mkCase "err/nargs15/pass14-nargs-greater" range14 (progSetC0Nargs 15 14),
    mkCase "ok/nargs15/pass15" range15 (progSetC0Nargs 15 15),

    -- c0 closure-stack merge via SETCONTVARARGS(copy=1).
    mkCase "ok/captured/more-minus1-pass1" #[intV 9] (progSetC0Captured 70 (-1) 1),
    mkCase "ok/captured/more-minus1-pass2" #[intV 9, intV 8] (progSetC0Captured 71 (-1) 2),
    mkCase "err/captured/more-minus1-pass2-underflow-one" #[intV 9] (progSetC0Captured 72 (-1) 2),
    mkCase "ok/captured/more0-pass1" #[intV 9, intV 8] (progSetC0Captured 73 0 1),
    mkCase "ok/captured/more1-pass1" #[intV 9] (progSetC0Captured 74 1 1),
    mkCase "err/captured/more1-pass0-nargs-greater" #[intV 9] (progSetC0Captured 75 1 0),
    mkCase "err/captured/more2-pass1-nargs-greater" #[intV 9, intV 10] (progSetC0Captured 76 2 1),
    mkCase "ok/captured/more2-pass3-threeargs" #[intV 9, intV 10, intV 11] (progSetC0Captured 77 2 3),
    mkCase "err/captured/more2-pass3-underflow-two" #[intV 9, intV 10] (progSetC0Captured 78 2 3),

    -- Decode errors around RETARGS prefix width.
    mkCaseCode "err/decode/truncated-8-prefix" #[] retArgsTruncated8Code,
    mkCaseCode "err/decode/truncated-15-prefix" #[intV 1] retArgsTruncated15Code
  ]

def suite : InstrSuite where
  id := retArgsId
  unit := #[
    { name := "unit/dispatch/retargs-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runRetArgsFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]

        expectOkStack "dispatch/matched-retargs"
          (runRetArgsFallback (retArgsInstr 1) #[intV 5, intV 6])
          #[intV 6] }
    ,
    { name := "unit/order/c0-reset-before-passargs-underflow"
      run := do
        let target : Continuation := c0NeedArgs 1
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawErr "retargs/passargs-underflow"
          (runRetArgsRawN 3 #[intV 9, intV 10] regs) .stkUnd
        if st.stack != #[intV 9, intV 10] then
          throw (IO.userError
            s!"retargs/passargs-underflow: expected stack unchanged, got {reprStr st.stack}")
        if st.cc != defaultCc then
          throw (IO.userError s!"retargs/passargs-underflow: expected cc unchanged, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"retargs/passargs-underflow: expected c0 reset, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/order/c0-reset-before-nargs-greater-check"
      run := do
        let target : Continuation := c0NeedArgs 2
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawErr "retargs/nargs-greater"
          (runRetArgsRawN 1 #[intV 4, intV 5] regs) .stkUnd
        if st.stack != #[intV 4, intV 5] then
          throw (IO.userError s!"retargs/nargs-greater: expected stack unchanged, got {reprStr st.stack}")
        if st.cc != defaultCc then
          throw (IO.userError s!"retargs/nargs-greater: expected cc unchanged, got {reprStr st.cc}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"retargs/nargs-greater: expected c0 reset, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/closure-merge-and-cdata-consumed"
      run := do
        let target : Continuation := c0Captured #[intV 100] 1
        let regs : Regs := { Regs.initial with c0 := target }
        let st ← expectRawOk "retargs/closure-merge"
          (runRetArgsRawN 3 #[intV 4, intV 5, intV 6] regs)
        if st.stack != #[intV 100, intV 6] then
          throw (IO.userError s!"retargs/closure-merge: expected #[100,6], got {reprStr st.stack}")
        match st.cc with
        | .envelope _ _ cdata =>
            if !cdata.stack.isEmpty || cdata.nargs != -1 then
              throw (IO.userError s!"retargs/closure-merge: expected consumed cdata, got {reprStr cdata}")
        | other =>
            throw (IO.userError s!"retargs/closure-merge: expected envelope continuation, got {reprStr other}")
        if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"retargs/closure-merge: expected c0 reset, got {reprStr st.regs.c0}") }
    ,
    { name := "unit/raw/malformed-high-arg-canonicalized-to-low-nibble"
      run := do
        -- C++ helper behavior: params := args & 15.
        let st ← expectRawOk "retargs/canonicalized"
          (runRetArgsRawN 16 #[intV 1, intV 2])
        if !st.stack.isEmpty then
          throw (IO.userError s!"retargs/canonicalized: expected empty stack (pass0), got {reprStr st.stack}")
        if st.cc != .quit 0 then
          throw (IO.userError s!"retargs/canonicalized: expected jump to quit0, got {reprStr st.cc}") }
    ,
    { name := "unit/opcode/decode-and-boundaries"
      run := do
        let code0 ←
          match assembleCp0 [retArgsInstr 0] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/retargs0 failed: {reprStr e}")
        let code15 ←
          match assembleCp0 [retArgsInstr 15] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble/retargs15 failed: {reprStr e}")
        if code0.bits != natToBits 0xdb20 16 then
          throw (IO.userError s!"opcode/retargs0: expected 0xdb20, got {reprStr code0.bits}")
        if code15.bits != natToBits 0xdb2f 16 then
          throw (IO.userError s!"opcode/retargs15: expected 0xdb2f, got {reprStr code15.bits}")

        expectDecodeRetArgs "decode/retargs0" (Cell.mkOrdinary (natToBits 0xdb20 16) #[]) 0
        expectDecodeRetArgs "decode/retargs15" (Cell.mkOrdinary (natToBits 0xdb2f 16) #[]) 15
        expectDecodeErr "decode/truncated-8" retArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" retArgsTruncated15Code .invOpcode

        let rawBits : BitString :=
          natToBits 0xdb1f 16 ++
          natToBits 0xdb20 16 ++
          natToBits 0xdb2f 16 ++
          natToBits 0xdb30 16
        let s0 := mkSliceFromBits rawBits
        let s1 ← expectDecodeStep "decode/raw-jmpxargs15" s0 (.jmpxArgs 15) 16
        let s2 ← expectDecodeStep "decode/raw-retargs0" s1 (.retArgs 0) 16
        let s3 ← expectDecodeStep "decode/raw-retargs15" s2 (.retArgs 15) 16
        let s4 ← expectDecodeStep "decode/raw-ret" s3 .ret 16
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/raw-end: expected exhausted bits, got {s4.bitsRemaining}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec retArgsId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RETARGS
