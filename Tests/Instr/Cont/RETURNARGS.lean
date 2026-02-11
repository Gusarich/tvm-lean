import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RETURNARGS

private def returnArgsId : InstrId := { name := "RETURNARGS" }

private def returnArgsInstr (count : Nat) : Instr := .returnArgs count

private def dispatchSentinel : Int := 49080

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def range14 : Array Value := intStackAsc 14
private def range15 : Array Value := intStackAsc 15
private def range16 : Array Value := intStackAsc 16

private def runReturnArgsDirect (count : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContReturnArgs (returnArgsInstr count) stack

private def runReturnArgsFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContReturnArgs instr (VM.push (intV dispatchSentinel)) stack

private def runReturnArgsRaw
    (instr : Instr)
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
  (execInstrContReturnArgs instr (pure ())).run st0

private def runReturnArgsRawN
    (count : Nat)
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1) : Except Excno Unit × VmState :=
  runReturnArgsRaw (returnArgsInstr count) stack cc c0 c1

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

private def expectDecodeReturnArgs
    (label : String)
    (code : Cell)
    (expectedCount : Nat)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .returnArgs expectedCount then
        throw (IO.userError s!"{label}: expected .returnArgs {expectedCount}, got {reprStr instr}")
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
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := returnArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseI
    (name : String)
    (stack : Array Value)
    (count : Nat)
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[returnArgsInstr count] fuel

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := returnArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (count : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .returnArgs count] ++ tail

private def progSetC0Nargs (n : Int) (count : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, .returnArgs count] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (count : Nat) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs,
    .popCtr 0, .returnArgs count] ++ tail

private def returnArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def returnArgsTruncated11Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed0 >>> 1) 11) #[]

private def returnArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed00 >>> 1) 15) #[]

private def oracleCases : Array OracleCase := #[
  -- Basic stack reshape behavior.
  mkCaseI "ok/basic/pass0-empty" #[] 0,
  mkCaseI "ok/basic/pass0-drop-one" #[intV 7] 0,
  mkCaseI "ok/basic/pass0-drop-mixed"
    #[.null, .cell cellA, .slice sliceB] 0,
  mkCaseI "ok/basic/pass1-exact-one" #[intV 7] 1,
  mkCaseI "ok/basic/pass1-keep-top-of-two" #[intV 7, intV 8] 1,
  mkCaseI "ok/basic/pass2-exact-two" #[intV 7, intV 8] 2,
  mkCaseI "ok/basic/pass2-drop-bottom-of-three" #[intV 7, intV 8, intV 9] 2,
  mkCaseI "ok/basic/pass3-keep-top-three-mixed"
    #[intV 1, .null, .cell cellA, .slice sliceA] 3,
  mkCaseI "ok/basic/pass4-keep-top-four" #[intV 1, intV 2, intV 3, intV 4, intV 5] 4,
  mkCaseI "ok/basic/pass14-drop-bottom16" range16 14,
  mkCaseI "ok/basic/pass15-exact-depth" range15 15,
  mkCaseI "ok/basic/pass15-drop-bottom16" range16 15,

  -- RETURNARGS does not jump; tail instructions continue.
  mkCase "ok/order/tail-exec-push"
    #[intV 9]
    #[returnArgsInstr 0, .pushInt (.num 77)],
  mkCase "ok/order/tail-exec-add"
    #[intV 2, intV 3, intV 4]
    #[returnArgsInstr 2, .add],
  mkCase "ok/order/program-leading-nop"
    #[intV 5]
    #[.nop, returnArgsInstr 1],
  mkCase "ok/order/program-two-returnargs"
    #[intV 1, intV 2, intV 3]
    #[returnArgsInstr 2, returnArgsInstr 1],
  mkCaseI "ok/order/pass2-preserves-top-order"
    #[intV 1, intV 2, intV 3, intV 4] 2,
  mkCaseI "ok/order/pass2-mixed-types"
    #[.cell cellA, .slice sliceA, .builder Builder.empty] 2,

  -- c0 retarget to c1 (quit1), then RETURNARGS updates c0 cdata.
  mkCase "ok/c0-from-c1/pass0" #[intV 11] (progSetC0FromC1 0),
  mkCase "ok/c0-from-c1/pass1" #[intV 11] (progSetC0FromC1 1),
  mkCase "ok/c0-from-c1/pass2-drop" #[intV 1, intV 2, intV 3] (progSetC0FromC1 2),
  mkCase "ok/c0-from-c1/tail-exec"
    #[intV 9]
    (progSetC0FromC1 0 #[.pushInt (.num 5)]),

  -- c0 nargs branch coverage (stkOv vs success).
  mkCase "ok/c0-nargs1/pass0-one-copied" #[intV 11] (progSetC0Nargs 1 0),
  mkCase "err/c0-nargs1/pass0-two-copied" #[intV 11, intV 12] (progSetC0Nargs 1 0),
  mkCase "ok/c0-nargs2/pass1-one-copied" #[intV 11, intV 12] (progSetC0Nargs 2 1),
  mkCase "err/c0-nargs0/pass0-one-copied" #[intV 11] (progSetC0Nargs 0 0),
  mkCase "ok/c0-nargs3/pass0-three-copied" #[intV 1, intV 2, intV 3] (progSetC0Nargs 3 0),
  mkCase "err/c0-nargs2/pass0-three-copied" #[intV 1, intV 2, intV 3] (progSetC0Nargs 2 0),
  mkCase "ok/c0-nargs15/pass15" range15 (progSetC0Nargs 15 15),
  mkCase "err/c0-nargs15/pass0-sixteen-copied" range16 (progSetC0Nargs 15 0),
  mkCase "err/c0-nargs2/pass3-underflow-before-stkov" #[intV 11, intV 12] (progSetC0Nargs 2 3),

  -- c0 already has captured stack via SETCONTVARARGS.
  mkCase "ok/captured/more-minus1-pass0-onecopy" #[intV 9] (progSetC0Captured 70 (-1) 0),
  mkCase "ok/captured/more1-pass0-onecopy" #[intV 9] (progSetC0Captured 71 1 0),
  mkCase "err/captured/more0-pass0-onecopy" #[intV 9] (progSetC0Captured 72 0 0),
  mkCase "ok/captured/more2-pass1-onecopy" #[intV 9, intV 10] (progSetC0Captured 73 2 1),
  mkCase "err/captured/more1-pass0-twocopy" #[intV 9, intV 10] (progSetC0Captured 74 1 0),
  mkCase "ok/captured/more2-pass0-twocopy" #[intV 9, intV 10] (progSetC0Captured 75 2 0),

  -- Underflow branches from check_underflow(count).
  mkCaseI "err/underflow/pass1-empty" #[] 1,
  mkCaseI "err/underflow/pass2-one" #[intV 1] 2,
  mkCaseI "err/underflow/pass15-depth14" range14 15,
  mkCaseI "err/underflow/pass15-empty" #[] 15,

  -- Decode boundaries around 12+4 RETURNARGS opcode.
  mkCaseCode "err/decode-truncated-8-prefix" #[] returnArgsTruncated8Code,
  mkCaseCode "err/decode-truncated-11-prefix" #[intV 1] returnArgsTruncated11Code,
  mkCaseCode "err/decode-truncated-15-prefix" #[intV 1] returnArgsTruncated15Code
]

def suite : InstrSuite where
  id := returnArgsId
  unit := #[
    { name := "unit/dispatch/returnargs-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-next-only"
          (runReturnArgsFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-returnargs"
          (runReturnArgsFallback (returnArgsInstr 1) #[intV 5, intV 6])
          #[intV 6] }
    ,
    { name := "unit/immediate/canonicalized-low-nibble"
      run := do
        expectOkStack "canonicalized/16-as-0"
          (runReturnArgsDirect 16 #[intV 1, intV 2])
          #[]
        let keepTop15 : Array Value := range16.extract 1 range16.size
        expectOkStack "canonicalized/31-as-15"
          (runReturnArgsDirect 31 range16)
          keepTop15
        expectOkStack "canonicalized/255-as-15"
          (runReturnArgsDirect 255 range16)
          keepTop15 }
    ,
    { name := "unit/errors/underflow-only"
      run := do
        expectErr "underflow/pass1-empty" (runReturnArgsDirect 1 #[]) .stkUnd
        expectErr "underflow/pass2-one" (runReturnArgsDirect 2 #[intV 1]) .stkUnd
        expectErr "underflow/pass15-depth14" (runReturnArgsDirect 15 range14) .stkUnd }
    ,
    { name := "unit/returnargs-common/c0-capture-bottom-preserve-top"
      run := do
        let st ← expectRawOk "c0-capture-bottom" (runReturnArgsRawN 1 #[intV 1, intV 2, intV 3])
        if st.stack != #[intV 3] then
          throw (IO.userError s!"c0-capture-bottom: expected stack #[3], got {reprStr st.stack}")
        else
          match st.regs.c0 with
          | .envelope ext _ cdata =>
              if ext != .quit 0 then
                throw (IO.userError s!"c0-capture-bottom: expected ext quit0, got {reprStr ext}")
              else if cdata.stack != #[intV 1, intV 2] then
                throw (IO.userError
                  s!"c0-capture-bottom: expected captured #[1,2], got {reprStr cdata.stack}")
              else if cdata.nargs != (-1) then
                throw (IO.userError s!"c0-capture-bottom: expected nargs=-1, got {cdata.nargs}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"c0-capture-bottom: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/returnargs-common/depth-equals-count-no-c0-wrap"
      run := do
        let st ← expectRawOk "depth-equals-count" (runReturnArgsRawN 2 #[intV 7, intV 8])
        if st.stack != #[intV 7, intV 8] then
          throw (IO.userError s!"depth-equals-count: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"depth-equals-count: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/order/stkov-after-stack-shape-and-before-c0-writeback"
      run := do
        let target := c0NeedArgs 1
        let st ← expectRawErr "stkov-order"
          (runReturnArgsRawN 0 #[intV 11, intV 12] (c0 := target)) .stkOv
        if !st.stack.isEmpty then
          throw (IO.userError s!"stkov-order: expected emptied stack after keep=0, got {reprStr st.stack}")
        else if st.regs.c0 != target then
          throw (IO.userError s!"stkov-order: expected c0 unchanged on error, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/raw/c0-target-ext-preserved"
      run := do
        let st ← expectRawOk "c0-ext-preserved"
          (runReturnArgsRawN 0 #[intV 9] (c0 := .quit 1))
        match st.regs.c0 with
        | .envelope ext _ cdata =>
            if ext != .quit 1 then
              throw (IO.userError s!"c0-ext-preserved: expected ext=quit1, got {reprStr ext}")
            else if cdata.stack != #[intV 9] then
              throw (IO.userError
                s!"c0-ext-preserved: expected captured #[9], got {reprStr cdata.stack}")
            else
              pure ()
        | other =>
            throw (IO.userError s!"c0-ext-preserved: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/decode-assemble/returnargs-opcode"
      run := do
        match assembleCp0 [.returnArgs 0] with
        | .ok assembled =>
            if assembled.bits != natToBits 0xed00 16 then
              throw (IO.userError s!"opcode/returnargs0: expected 0xed00, got {reprStr assembled.bits}")
        | .error e =>
            throw (IO.userError s!"opcode/returnargs0: unexpected assembly error {reprStr e}")

        match assembleCp0 [.returnArgs 15] with
        | .ok assembled =>
            if assembled.bits != natToBits 0xed0f 16 then
              throw (IO.userError s!"opcode/returnargs15: expected 0xed0f, got {reprStr assembled.bits}")
        | .error e =>
            throw (IO.userError s!"opcode/returnargs15: unexpected assembly error {reprStr e}")

        match assembleCp0 [.returnArgs 16] with
        | .error e =>
            if e != .rangeChk then
              throw (IO.userError s!"opcode/returnargs16: expected rangeChk, got {e}")
        | .ok assembled =>
            throw (IO.userError s!"opcode/returnargs16: expected assemble error, got {reprStr assembled.bits}")

        expectDecodeReturnArgs "decode/ok-0" (Cell.mkOrdinary (natToBits 0xed00 16) #[]) 0
        expectDecodeReturnArgs "decode/ok-15" (Cell.mkOrdinary (natToBits 0xed0f 16) #[]) 15
        expectDecodeErr "decode/truncated-8" returnArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-11" returnArgsTruncated11Code .invOpcode
        expectDecodeErr "decode/truncated-15" returnArgsTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkReplayOracleFuzzSpec returnArgsId 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RETURNARGS
