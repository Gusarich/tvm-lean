import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.JMPXARGS

private def jmpxArgsId : InstrId := { name := "JMPXARGS" }
private def jmpxArgsInstr (params : Nat) : Instr := .jmpxArgs params
private def dispatchSentinel : Int := 73194

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def jmpxArgsCode0 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb10 16) #[]

private def jmpxArgsCode15 : Cell :=
  Cell.mkOrdinary (natToBits 0xdb1f 16) #[]

private def jmpxArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xdb 8) #[]

private def jmpxArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xdb10 >>> 1) 15) #[]

private def emptyCode : Cell :=
  Cell.empty

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def mkStack (below : Array Value) (cont : Value := q0) : Array Value :=
  below ++ #[cont]

private def mkOrdCont
    (nargs : Int := -1)
    (captured : Array Value := #[]) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) (.quit 0) OrdCregs.empty { stack := captured, nargs := nargs }

private def runJmpxArgsDirect (params : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrFlowJmpxArgs (jmpxArgsInstr params) stack

private def runJmpxArgsDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrFlowJmpxArgs instr (VM.push (intV dispatchSentinel)) stack

private def runJmpxArgsRaw
    (params : Nat)
    (stack : Array Value)
    (cc : Continuation := .quit 0)
    (gas : GasLimits := GasLimits.default) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc, gas := gas }
  (execInstrFlowJmpxArgs (jmpxArgsInstr params) (pure ())).run st0

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
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeJmpxArgs
    (label : String)
    (code : Cell)
    (expectedParams : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .jmpxArgs expectedParams then
        throw (IO.userError s!"{label}: expected .jmpxArgs {expectedParams}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits={expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxArgsId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := jmpxArgsId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkJumpCase
    (name : String)
    (params : Nat)
    (below : Array Value)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name (mkStack below) (#[jmpxArgsInstr params] ++ tail) gasLimits fuel

private def progSetNumThenJmp (more : Int) (params : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num more), .setNumVarArgs, .jmpxArgs params] ++ tail

private def progCaptureThenJmp (copy : Nat) (more : Int) (params : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .setContArgs copy more, .jmpxArgs params] ++ tail

private def depth15 : Array Value := intStackAsc 15
private def depth16 : Array Value := intStackAsc 16

private def jmpxArgsGasExact : Int :=
  computeExactGasBudget (jmpxArgsInstr 0)

private def jmpxArgsGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (jmpxArgsInstr 0)

private def oracleCases : Array OracleCase := #[
  -- Pass-args shaping for plain continuations.
  mkJumpCase "ok/pass0/empty" 0 #[],
  mkJumpCase "ok/pass0/drop-one" 0 #[intV 7],
  mkJumpCase "ok/pass0/drop-mixed" 0 #[.null, .cell cellA, .slice sliceA],
  mkJumpCase "ok/pass1/exact-one" 1 #[intV 7],
  mkJumpCase "ok/pass1/keep-top-of-two" 1 #[intV 7, intV 8],
  mkJumpCase "ok/pass2/exact-two" 2 #[intV 7, intV 8],
  mkJumpCase "ok/pass2/drop-bottom-of-three" 2 #[intV 7, intV 8, intV 9],
  mkJumpCase "ok/pass3/keep-top-three-mixed" 3 #[intV 1, .null, .cell cellA, .slice sliceA],
  mkJumpCase "ok/pass15/exact-depth" 15 depth15,
  mkJumpCase "ok/pass15/drop-bottom" 15 depth16,

  -- Ordering: jump is terminal for the current instruction stream.
  mkJumpCase "order/tail-skipped/push" 0 #[] #[.pushInt (.num 777)],
  mkJumpCase "order/tail-skipped/add-underflow" 0 #[] #[.add],
  mkCase "order/prelude/push-swap-jmpxargs1"
    #[q0]
    #[.pushInt (.num 9), .xchg0 1, .jmpxArgs 1, .add],
  mkCase "order/prelude/push-push-jmpxargs2"
    #[q0]
    #[.pushInt (.num 4), .pushInt (.num 5), .xchg0 1, .xchg0 1, .jmpxArgs 2, .add],
  mkCase "order/prelude/deep-and-tail"
    #[intV 5, q0]
    #[.pushInt (.num 7), .xchg0 1, .jmpxArgs 1, .pushInt (.num 55)],

  -- Runtime pop/type/underflow branches.
  mkCase "err/underflow/empty-stack" #[] #[.jmpxArgs 0],
  mkCase "err/type/top-int" #[intV 1] #[.jmpxArgs 1],
  mkCase "err/type/top-null" #[.null] #[.jmpxArgs 1],
  mkCase "err/type/top-cell" #[.cell cellA] #[.jmpxArgs 1],
  mkCase "err/type/top-slice" #[.slice sliceB] #[.jmpxArgs 1],
  mkCase "err/type/top-builder" #[.builder Builder.empty] #[.jmpxArgs 1],
  mkCase "err/type/top-tuple" #[.tuple #[]] #[.jmpxArgs 1],
  mkCase "err/underflow/pass1-after-pop" #[q0] #[.jmpxArgs 1],
  mkCase "err/underflow/pass2-after-pop" #[intV 1, q0] #[.jmpxArgs 2],
  mkCase "err/order/type-before-pass-underflow" #[q0, intV 1] #[.jmpxArgs 2],
  mkCase "err/order/pass-underflow-before-below-type" #[.null, q0] #[.jmpxArgs 2],

  -- Jump-time `nargs` checks via SETNUMVARARGS.
  mkCase "ok/nargs1/pass1" #[intV 7] (progSetNumThenJmp 1 1),
  mkCase "ok/nargs0/pass0" #[] (progSetNumThenJmp 0 0),
  mkCase "err/nargs1/pass0" #[] (progSetNumThenJmp 1 0),
  mkCase "err/nargs2/pass1" #[intV 1, intV 2] (progSetNumThenJmp 2 1),
  mkCase "ok/nargs2/pass2" #[intV 1, intV 2] (progSetNumThenJmp 2 2),
  mkCase "err/nargs255/pass15-depth14" (intStackAsc 14) (progSetNumThenJmp 255 15),
  mkCase "err/nargs255/pass15-depth15" depth15 (progSetNumThenJmp 255 15),
  mkCase "order/nargs1/tail-skipped" #[intV 8] (progSetNumThenJmp 1 1 #[.pushInt (.num 999)]),

  -- Captured-stack interactions via SETCONTARGS + jump-time behavior.
  mkCase "ok/captured/copy2-pass1"
    #[intV 1, intV 2, intV 3]
    (progCaptureThenJmp 2 (-1) 1),
  mkCase "err/captured/copy2-pass1-underflow"
    #[intV 1, intV 2]
    (progCaptureThenJmp 2 (-1) 1),
  mkCase "ok/captured/copy2-more1-pass3"
    #[intV 1, intV 2, intV 3, intV 4, intV 5]
    (progCaptureThenJmp 2 1 3),
  mkCase "err/captured/copy2-more2-pass1"
    #[intV 1, intV 2, intV 3]
    (progCaptureThenJmp 2 2 1),
  mkCase "order/captured/tail-skipped"
    #[intV 1, intV 2, intV 3]
    (progCaptureThenJmp 2 (-1) 1 #[.pushInt (.num 1001)]),

  -- Decode boundaries for 16-bit fixed opcode.
  mkCodeCase "ok/decode/exact-param0" #[q0] jmpxArgsCode0,
  mkCodeCase "ok/decode/exact-param15" (depth15 ++ #[q0]) jmpxArgsCode15,
  mkCodeCase "err/decode/truncated-8" #[q0] jmpxArgsTruncated8Code,
  mkCodeCase "err/decode/truncated-15" (#[intV 1, q0]) jmpxArgsTruncated15Code,
  mkCodeCase "err/decode/empty" #[q0] emptyCode,
  mkCodeCase "err/decode/truncated-15-mixed" #[.cell cellB, .slice sliceA, q0] jmpxArgsTruncated15Code,

  -- Gas boundary probes on the JMPXARGS opcode itself.
  mkCase "gas/exact-cost-succeeds"
    #[q0]
    #[.pushInt (.num jmpxArgsGasExact), .tonEnvOp .setGasLimit, .jmpxArgs 0],
  mkCase "gas/exact-minus-one-out-of-gas"
    #[q0]
    #[.pushInt (.num jmpxArgsGasExactMinusOne), .tonEnvOp .setGasLimit, .jmpxArgs 0]
]

def suite : InstrSuite where
  id := jmpxArgsId
  unit := #[
    { name := "unit/dispatch/jmpxargs-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runJmpxArgsDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-jmpxargs"
          (runJmpxArgsDispatchFallback (.jmpxArgs 0) #[q0])
          #[] }
    ,
    { name := "unit/direct/pass-args-shaping"
      run := do
        expectOkStack "direct/pass0-drops-all"
          (runJmpxArgsDirect 0 (mkStack #[intV 1]))
          #[]
        expectOkStack "direct/pass2-keeps-top-two"
          (runJmpxArgsDirect 2 (mkStack #[intV 1, intV 2, intV 3]))
          #[intV 2, intV 3]
        expectOkStack "direct/pass15-drops-bottom-one"
          (runJmpxArgsDirect 15 (mkStack depth16))
          (depth16.extract 1 16) }
    ,
    { name := "unit/error/pop-order-and-pass-underflow"
      run := do
        expectErr "underflow/empty"
          (runJmpxArgsDirect 0 #[])
          .stkUnd
        expectErr "type/top-int-before-pass-check"
          (runJmpxArgsDirect 2 #[intV 1])
          .typeChk
        expectErr "underflow/pass1-after-pop"
          (runJmpxArgsDirect 1 #[q0])
          .stkUnd
        expectErr "order/type-before-underflow"
          (runJmpxArgsDirect 2 #[q0, intV 1])
          .typeChk
        expectErr "order/underflow-before-below-type"
          (runJmpxArgsDirect 2 #[.null, q0])
          .stkUnd }
    ,
    { name := "unit/raw/regression/no-pretruncate-on-jump-error"
      run := do
        let contNeed2 : Continuation := mkOrdCont 2 #[]
        let cc0 : Continuation := .quit 99
        let st1 ← expectRawErr "raw/nargs>pass" (runJmpxArgsRaw 1 #[intV 1, intV 2, .cont contNeed2] cc0) .stkUnd
        if st1.stack != #[intV 1, intV 2] then
          throw (IO.userError s!"raw/nargs>pass: stack changed unexpectedly: {reprStr st1.stack}")
        if st1.cc != cc0 then
          throw (IO.userError s!"raw/nargs>pass: cc changed unexpectedly: {reprStr st1.cc}")

        let st2 ← expectRawErr "raw/nargs>pass-second-check"
          (runJmpxArgsRaw 1 #[intV 1, intV 2, intV 3, .cont contNeed2] cc0)
          .stkUnd
        if st2.stack != #[intV 1, intV 2, intV 3] then
          throw (IO.userError s!"raw/nargs>pass-second-check: stack changed unexpectedly: {reprStr st2.stack}")
        if st2.cc != cc0 then
          throw (IO.userError s!"raw/nargs>pass-second-check: cc changed unexpectedly: {reprStr st2.cc}") }
    ,
    { name := "unit/raw/captured-stack-applied-at-jump-time"
      run := do
        let contCaptured : Continuation := mkOrdCont (-1) #[intV 8, intV 9]
        let st ← expectRawOk "raw/captured-pass1" (runJmpxArgsRaw 1 #[intV 1, intV 2, .cont contCaptured])
        if st.stack != #[intV 8, intV 9, intV 2] then
          throw (IO.userError s!"raw/captured-pass1: expected #[8,9,2], got {reprStr st.stack}") }
    ,
    { name := "unit/decode/exact-and-truncated-prefixes"
      run := do
        expectDecodeJmpxArgs "decode/exact-param0" jmpxArgsCode0 0
        expectDecodeJmpxArgs "decode/exact-param15" jmpxArgsCode15 15
        expectDecodeErr "decode/truncated-8" jmpxArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" jmpxArgsTruncated15Code .invOpcode
        expectDecodeErr "decode/empty" emptyCode .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.JMPXARGS
