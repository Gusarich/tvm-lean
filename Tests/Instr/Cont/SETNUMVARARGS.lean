import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.SETNUMVARARGS

private def setNumVarArgsId : InstrId := { name := "SETNUMVARARGS" }
private def setNumVarArgsInstr : Instr := .setNumVarArgs
private def dispatchSentinel : Int := 49261

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def fullSliceA : Slice := Slice.ofCell cellA

private def mkStack (below : Array Value) (more : Int) (cont : Value := q0) : Array Value :=
  below ++ #[cont, intV more]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat i))
    out

private def range255 : Array Value := intStackAsc 255

private def runSetNumVarArgsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContSetNumVarArgs setNumVarArgsInstr stack

private def runSetNumVarArgsFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContSetNumVarArgs instr (VM.push (intV dispatchSentinel)) stack

private def runSetNumVarArgsRaw
    (stack : Array Value)
    (instr : Instr := setNumVarArgsInstr) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContSetNumVarArgs instr (pure ())).run st0

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

private def expectDecodeSetNumVarArgs
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .setNumVarArgs then
        throw (IO.userError s!"{label}: expected .setNumVarArgs, got {reprStr instr}")
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
    (program : Array Instr := #[setNumVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setNumVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := setNumVarArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetNumThenJmp (more params : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num more), .setNumVarArgs, .pushInt (.num params), .jmpxVarArgs] ++ tail

private def progSetNumTwiceThenJmp (more1 more2 params : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 0, .pushInt (.num more1), .setNumVarArgs,
    .pushInt (.num more2), .setNumVarArgs,
    .pushInt (.num params), .jmpxVarArgs] ++ tail

private def setNumVarArgsExactCode : Cell :=
  Cell.mkOrdinary (natToBits 0xed12 16) #[]

private def setNumVarArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def setNumVarArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed12 >>> 1) 15) #[]

private def setNumVarArgsMoreOkPool : Array Int :=
  #[-1, 0, 1, 2, 255]

private def setNumVarArgsMoreRangeErrPool : Array Int :=
  #[-2, 256, maxInt257, minInt257]

private def setNumVarArgsBadMorePool : Array Value :=
  #[.null, .cell cellA, .slice fullSliceA, .builder Builder.empty, .tuple #[], q0]

private def setNumVarArgsBadContPool : Array Value :=
  #[.null, .cell cellA, .slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def setNumVarArgsNoiseValuePool : Array Value :=
  #[.null, intV 1, intV (-1), .cell cellA, .slice fullSliceA, .builder Builder.empty, .tuple #[]]

private def pickFromPool {a : Type} [Inhabited a] (pool : Array a) (rng : StdGen) : a × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genBelowStack (count : Nat) (rng0 : StdGen) : Array Value × StdGen := Id.run do
  let mut out : Array Value := #[]
  let mut rng := rng0
  for _ in [0:count] do
    let (v, rng') := pickFromPool setNumVarArgsNoiseValuePool rng
    out := out.push v
    rng := rng'
  return (out, rng)

private def genSetNumVarArgsFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 23
  let (depth, rng2) := randNat rng1 0 4
  let (below, rng3) := genBelowStack depth rng2
  let (moreOk, rng4) := pickFromPool setNumVarArgsMoreOkPool rng3
  let (moreRangeErr, rng5) := pickFromPool setNumVarArgsMoreRangeErrPool rng4
  let (badMore, rng6) := pickFromPool setNumVarArgsBadMorePool rng5
  let (badCont, rng7) := pickFromPool setNumVarArgsBadContPool rng6
  let base :=
    if shape = 0 then
      mkCase s!"fuzz/ok/basic/more-{moreOk}/deep-{depth}" (mkStack below moreOk)
    else if shape = 1 then
      mkCase s!"fuzz/ok/basic/trailing-push/deep-{depth}"
        (mkStack (below ++ #[intV 7]) 0)
        #[setNumVarArgsInstr, .pushInt (.num 777)]
    else if shape = 2 then
      mkCase "fuzz/ok/basic/trailing-add-runs"
        (mkStack #[intV 2, intV 3] (-1))
        #[setNumVarArgsInstr, .popCtr 0, .pushInt (.num 4), .add]
    else if shape = 3 then
      mkCase "fuzz/err/underflow/empty" #[]
    else if shape = 4 then
      mkCase "fuzz/err/underflow/one-item" #[q0]
    else if shape = 5 then
      mkCase s!"fuzz/err/type/more/deep-{depth}" (below ++ #[q0, badMore])
    else if shape = 6 then
      mkCase "fuzz/err/type/cont" (mkStack #[] 0 badCont)
    else if shape = 7 then
      mkCase s!"fuzz/err/range/more-{moreRangeErr}" (mkStack below moreRangeErr)
    else if shape = 8 then
      mkCase "fuzz/err/range/more-nan-via-program"
        #[q0]
        #[.pushInt .nan, setNumVarArgsInstr]
    else if shape = 9 then
      mkCase "fuzz/err/order/range-before-cont-type" (mkStack #[] 256 badCont)
    else if shape = 10 then
      mkCase "fuzz/err/order/type-more-before-cont-type" #[badCont, .null]
    else if shape = 11 then
      mkCase "fuzz/err/order/nan-before-cont-type"
        #[badCont]
        #[.pushInt .nan, setNumVarArgsInstr]
    else if shape = 12 then
      mkCaseCode "fuzz/ok/decode/exact-opcode-cell" (mkStack #[] 0) setNumVarArgsExactCode
    else if shape = 13 then
      mkCaseCode "fuzz/err/decode/truncated-8-prefix" (mkStack #[] 0) setNumVarArgsTruncated8Code
    else if shape = 14 then
      mkCaseCode "fuzz/err/decode/truncated-15-prefix" (mkStack #[intV 1] 0) setNumVarArgsTruncated15Code
    else if shape = 15 then
      mkCase "fuzz/ok/jmp/more-minus1-pass0-empty" #[] (progSetNumThenJmp (-1) 0)
    else if shape = 16 then
      mkCase "fuzz/ok/jmp/more1-pass1-onearg" #[intV 7] (progSetNumThenJmp 1 1)
    else if shape = 17 then
      mkCase "fuzz/err/jmp/more1-pass0" #[] (progSetNumThenJmp 1 0)
    else if shape = 18 then
      mkCase "fuzz/err/jmp/more2-pass1" #[intV 1, intV 2] (progSetNumThenJmp 2 1)
    else if shape = 19 then
      mkCase "fuzz/ok/jmp/more255-passminus1-depth255" range255 (progSetNumThenJmp 255 (-1))
    else if shape = 20 then
      mkCase "fuzz/err/jmp/more255-passminus1-underflow" #[] (progSetNumThenJmp 255 (-1))
    else if shape = 21 then
      mkCase "fuzz/order/jmp-tail-skipped-after-setnum"
        #[intV 41]
        (progSetNumThenJmp 1 1 #[.pushInt (.num 999)])
    else if shape = 22 then
      mkCase "fuzz/ok/jmp/twice-more1-then2-pass1-keeps-nargs1"
        #[intV 9]
        (progSetNumTwiceThenJmp 1 2 1)
    else
      mkCase "fuzz/err/jmp/twice-more3-then1-sentinel-underflow"
        #[]
        (progSetNumTwiceThenJmp 3 1 (-1))
  let (tag, rng8) := randNat rng7 0 999_999
  ({ base with name := s!"{base.name}/{tag}" }, rng8)

private def oracleCases : Array OracleCase := #[
  -- Basic behavior (`more` is popped; continuation remains on stack).
  mkCase "ok/basic/more-minus1-empty" (mkStack #[] (-1)),
  mkCase "ok/basic/more-minus1-below-int" (mkStack #[intV 7] (-1)),
  mkCase "ok/basic/more-minus1-below-mixed"
    (mkStack #[.null, .cell cellA, .slice fullSliceA, .builder Builder.empty, .tuple #[]] (-1)),
  mkCase "ok/basic/more0-empty" (mkStack #[] 0),
  mkCase "ok/basic/more0-below-one" (mkStack #[intV 11] 0),
  mkCase "ok/basic/more1-below-one" (mkStack #[intV 12] 1),
  mkCase "ok/basic/more2-below-two" (mkStack #[intV 21, intV 22] 2),
  mkCase "ok/basic/more255-below-three" (mkStack #[intV 31, intV 32, intV 33] 255),
  mkCase "ok/basic/trailing-push-runs"
    (mkStack #[intV 7] 0)
    #[setNumVarArgsInstr, .pushInt (.num 777)],
  mkCase "ok/basic/trailing-add-runs"
    (mkStack #[intV 2, intV 3] (-1))
    #[setNumVarArgsInstr, .popCtr 0, .pushInt (.num 4), .add],

  -- Pop/type/range failures.
  mkCase "err/underflow/empty" #[],
  mkCase "err/underflow/one-item" #[q0],
  mkCase "err/type/more-null" #[q0, .null],
  mkCase "err/type/more-cell" #[q0, .cell cellA],
  mkCase "err/type/more-slice" #[q0, .slice fullSliceA],
  mkCase "err/type/more-builder" #[q0, .builder Builder.empty],
  mkCase "err/type/more-tuple" #[q0, .tuple #[]],
  mkCase "err/type/more-cont" #[q0, q0],
  mkCase "err/type/cont-null" (mkStack #[] 0 .null),
  mkCase "err/type/cont-cell" (mkStack #[] 0 (.cell cellA)),
  mkCase "err/type/cont-slice" (mkStack #[] 0 (.slice fullSliceA)),
  mkCase "err/type/cont-builder" (mkStack #[] 0 (.builder Builder.empty)),
  mkCase "err/type/cont-tuple" (mkStack #[] 0 (.tuple #[])),
  mkCase "err/range/more-minus2" (mkStack #[] (-2)),
  mkCase "err/range/more-256" (mkStack #[] 256),
  mkCase "err/range/more-max-int257" (mkStack #[] maxInt257),
  mkCase "err/range/more-min-int257" (mkStack #[] minInt257),
  mkCase "err/range/more-nan-via-program"
    #[q0]
    #[.pushInt .nan, setNumVarArgsInstr],

  -- Error ordering: `more` decode/range happens before continuation type checks.
  mkCase "err/order/range-before-cont-type" (mkStack #[] 256 .null),
  mkCase "err/order/type-more-before-cont-type" #[.null, .null],
  mkCase "err/order/nan-before-cont-type"
    #[.null]
    #[.pushInt .nan, setNumVarArgsInstr],

  -- Decode boundaries around the 16-bit opcode.
  mkCaseCode "ok/decode/exact-opcode-cell" (mkStack #[] 0) setNumVarArgsExactCode,
  mkCaseCode "err/decode/truncated-8-prefix" (mkStack #[] 0) setNumVarArgsTruncated8Code,
  mkCaseCode "err/decode/truncated-15-prefix" (mkStack #[intV 1] 0) setNumVarArgsTruncated15Code,

  -- Vararg effects via jump integration (`nargs` produced by SETNUMVARARGS).
  mkCase "ok/jmp/more-minus1-pass0-empty" #[] (progSetNumThenJmp (-1) 0),
  mkCase "ok/jmp/more0-pass0-empty" #[] (progSetNumThenJmp 0 0),
  mkCase "err/jmp/more1-pass0" #[] (progSetNumThenJmp 1 0),
  mkCase "ok/jmp/more1-pass1-onearg" #[intV 7] (progSetNumThenJmp 1 1),
  mkCase "err/jmp/more1-passminus1-noarg" #[] (progSetNumThenJmp 1 (-1)),
  mkCase "err/jmp/more2-pass1" #[intV 1, intV 2] (progSetNumThenJmp 2 1),
  mkCase "ok/jmp/more2-pass2" #[intV 1, intV 2] (progSetNumThenJmp 2 2),
  mkCase "err/jmp/more255-passminus1-underflow" #[] (progSetNumThenJmp 255 (-1)),
  mkCase "ok/jmp/more255-passminus1-depth255" range255 (progSetNumThenJmp 255 (-1)),
  mkCase "order/jmp-tail-skipped-after-setnum" #[intV 41]
    (progSetNumThenJmp 1 1 #[.pushInt (.num 999)]),
  mkCase "err/jmp/twice-more3-then1-sentinel-underflow" #[] (progSetNumTwiceThenJmp 3 1 (-1)),
  mkCase "ok/jmp/twice-more1-then2-pass1-keeps-nargs1" #[intV 9] (progSetNumTwiceThenJmp 1 2 1),
  mkCase "ok/jmp/twice-more0-then2-pass0-keeps-nargs0" #[] (progSetNumTwiceThenJmp 0 2 0),
  mkCase "err/jmp/twice-more2-then-minus1-pass1-still2"
    #[intV 5, intV 6]
    (progSetNumTwiceThenJmp 2 (-1) 1)
]

def suite : InstrSuite where
  id := setNumVarArgsId
  unit := #[
    { name := "unit/dispatch/setnum-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runSetNumVarArgsFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-setnum"
          (runSetNumVarArgsFallback setNumVarArgsInstr (mkStack #[] (-1)))
          #[q0] }
    ,
    { name := "unit/decode/exact-and-truncated"
      run := do
        expectDecodeSetNumVarArgs "decode/exact" setNumVarArgsExactCode
        expectDecodeErr "decode/truncated-8" setNumVarArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" setNumVarArgsTruncated15Code .invOpcode }
    ,
    { name := "unit/errors/type-range-underflow-and-nan"
      run := do
        expectErr "underflow/empty" (runSetNumVarArgsDirect #[]) .stkUnd
        expectErr "underflow/one-item" (runSetNumVarArgsDirect #[q0]) .stkUnd
        expectErr "type/more-null" (runSetNumVarArgsDirect #[q0, .null]) .typeChk
        expectErr "range/more-minus2" (runSetNumVarArgsDirect (mkStack #[] (-2))) .rangeChk
        expectErr "range/more-256" (runSetNumVarArgsDirect (mkStack #[] 256)) .rangeChk
        expectErr "range/more-nan" (runSetNumVarArgsDirect #[q0, .int .nan]) .rangeChk
        expectErr "type/cont-null" (runSetNumVarArgsDirect (mkStack #[] 0 .null)) .typeChk }
    ,
    { name := "unit/order/range-before-cont-type-and-pop-state"
      run := do
        let st ← expectRawErr "order/range-before-type"
          (runSetNumVarArgsRaw (mkStack #[] 256 .null)) .rangeChk
        if st.stack != #[.null] then
          throw (IO.userError
            s!"order/range-before-type: expected remaining stack #[null], got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/order/cont-type-pops-both-more-and-cont"
      run := do
        let st ← expectRawErr "order/cont-type-pop"
          (runSetNumVarArgsRaw (mkStack #[] 0 .null)) .typeChk
        if !st.stack.isEmpty then
          throw (IO.userError
            s!"order/cont-type-pop: expected empty stack after pops, got {reprStr st.stack}")
        else
          pure () }
    ,
    { name := "unit/cont/more-minus1-keeps-quit"
      run := do
        let st ← expectRawOk "cont/more-minus1" (runSetNumVarArgsRaw (mkStack #[] (-1)))
        match st.stack with
        | #[.cont (.quit 0)] => pure ()
        | _ =>
            throw (IO.userError
              s!"cont/more-minus1: expected top continuation quit(0), got {reprStr st.stack}") }
    ,
    { name := "unit/cont/more0-wraps-quit-and-sets-nargs0"
      run := do
        let st ← expectRawOk "cont/more0" (runSetNumVarArgsRaw (mkStack #[] 0))
        match st.stack with
        | #[.cont (.envelope ext _ cdata)] =>
            if ext != .quit 0 then
              throw (IO.userError s!"cont/more0: expected ext quit(0), got {reprStr ext}")
            else if cdata.nargs != 0 then
              throw (IO.userError s!"cont/more0: expected nargs=0, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"cont/more0: expected wrapped envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/cont/nargs-neg-becomes-more"
      run := do
        let cont : Continuation := .envelope (.quit 9) OrdCregs.empty { stack := #[], nargs := -1 }
        let st ← expectRawOk "cont/nargs-neg" (runSetNumVarArgsRaw (mkStack #[] 7 (.cont cont)))
        match st.stack with
        | #[.cont (.envelope ext _ cdata)] =>
            if ext != .quit 9 then
              throw (IO.userError s!"cont/nargs-neg: expected ext quit(9), got {reprStr ext}")
            else if cdata.nargs != 7 then
              throw (IO.userError s!"cont/nargs-neg: expected nargs=7, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError s!"cont/nargs-neg: expected envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/cont/nargs-gt-more-clamps-sentinel"
      run := do
        let cont : Continuation := .envelope (.quit 7) OrdCregs.empty { stack := #[], nargs := 3 }
        let st ← expectRawOk "cont/nargs-clamp" (runSetNumVarArgsRaw (mkStack #[] 1 (.cont cont)))
        match st.stack with
        | #[.cont (.envelope _ _ cdata)] =>
            if cdata.nargs != 0x40000000 then
              throw (IO.userError s!"cont/nargs-clamp: expected sentinel nargs, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"cont/nargs-clamp: expected envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/cont/nargs-nonneg-unchanged-when-more-higher"
      run := do
        let cont : Continuation := .envelope (.quit 5) OrdCregs.empty { stack := #[], nargs := 0 }
        let st ← expectRawOk "cont/nargs-unchanged" (runSetNumVarArgsRaw (mkStack #[] 2 (.cont cont)))
        match st.stack with
        | #[.cont (.envelope _ _ cdata)] =>
            if cdata.nargs != 0 then
              throw (IO.userError s!"cont/nargs-unchanged: expected nargs=0, got {cdata.nargs}")
            else
              pure ()
        | _ =>
            throw (IO.userError
              s!"cont/nargs-unchanged: expected envelope continuation, got {reprStr st.stack}") }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[
    { seed := fuzzSeedForInstr setNumVarArgsId
      count := 500
      gen := genSetNumVarArgsFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cont.SETNUMVARARGS
