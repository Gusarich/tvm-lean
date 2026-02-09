import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.PUSHINT_LONG

/-
PUSHINT_LONG branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Stack/PushInt.lean`
    (`execInstrStackPushInt`, `.pushInt` dispatch and `.nan`/`.num` split)
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`VM.pushIntQuiet`, signed-257 overflow gate)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`encodeCp0` integer ladder, long path `0x82 + len5 + value`, 259-bit upper bound)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`decodeCp0WithBits` `b8=0x82` arm, reserved `len5=31`, payload-length checks)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_push_int`, `compute_len_push_int`, opcode registration `mkextrange(0x82<<5, ..., 13, 5)`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`Stack::push_int`, signed-257 overflow throw `int_ov`)

Branch map used for this suite:
- Lean execution path: 4 branch points / 6 terminal outcomes
  (dispatch/fallback; `.nan` vs `.num`; signed-257 fit success vs `intOv`).
- Lean codec path (long arm): 6 branch points / 9 terminal outcomes
  (`0x82` match; reserved `len5=31`; payload availability; decode success;
   encode ladder to long arm and 259-bit fit gate).
- C++ aligned path: 5 branch points / 8 terminal outcomes
  (`mkextrange` route; bit-availability check; integer fetch; `push_int` fit/overflow;
   computed-length gate for decoder cursor advance).

Key risk areas covered:
- 16-bit/long boundary (`32767`/`32768`, `-32768`/`-32769`);
- signed-257 acceptance window (`minInt257..maxInt257`) and immediate `intOv` outside it;
- long-prefix integrity (reserved `len5=31`, truncated payload rejection);
- stack-order preservation (existing values remain below the pushed constant);
- prelude-injection discipline for non-serializable prep values (NaN/out-of-range)
  via `oracleIntInputsToStackOrProgram`, never raw oracle stack tokens;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def pushintLongId : InstrId := { name := "PUSHINT_LONG" }

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkPushLongInstr (n : Int) : Instr :=
  .pushInt (.num n)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := pushintLongId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkPushLongCase
    (name : String)
    (n : Int)
    (stack : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  mkCase name stack #[mkPushLongInstr n] gasLimits fuel

private def mkPreludePushLongCase
    (name : String)
    (preludeVals : Array IntVal)
    (n : Int)
    (tail : Array Instr := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, programPrefix) := oracleIntInputsToStackOrProgram preludeVals
  mkCase name stack (programPrefix ++ #[mkPushLongInstr n] ++ tail) gasLimits fuel

private def runPushLongDirect (n : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackPushInt (mkPushLongInstr n) stack

private def runPushLongDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackPushInt instr (VM.push (intV 6060)) stack

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .error e =>
      throw (IO.userError s!"{label}: decode failed with {e}")
  | .ok (instr, bits, s') =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure s'

private def expectDecodeErr (label : String) (s : Slice) (expected : Excno) : IO Unit := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error {expected}, got {reprStr instr} ({bits} bits)")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")

private def expectAssembleErr (label : String) (program : List Instr) (expected : Excno) : IO Unit := do
  match assembleCp0 program with
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")

private def pushLongGasProbeValue : Int := pow2 40

private def pushLongSetGasExact : Int :=
  computeExactGasBudget (mkPushLongInstr pushLongGasProbeValue)

private def pushLongSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne (mkPushLongInstr pushLongGasProbeValue)

private def mkGasCase (name : String) (budget : Int) : OracleCase :=
  mkCase name #[] #[.pushInt (.num budget), .tonEnvOp .setGasLimit, mkPushLongInstr pushLongGasProbeValue]

private def longInRangePool : Array Int :=
  #[
    32768, 32769, 65535, 65536,
    -32769, -32770, -65535, -65536,
    pow2 32, -(pow2 32),
    pow2 64, -(pow2 64),
    pow2 128, -(pow2 128),
    maxInt257, maxInt257 - 1,
    minInt257, minInt257 + 1
  ]

private def longOverflowPool : Array Int :=
  #[
    maxInt257 + 1,
    maxInt257 + 2,
    minInt257 - 1,
    minInt257 - 2,
    pow2 257,
    -(pow2 257),
    (pow2 258) - 1,
    -(pow2 258)
  ]

private def forceLongImmediate (n : Int) : Int :=
  if (-32768 ≤ n ∧ n ≤ 32767) then
    if n ≥ 0 then n + 32768 else n - 32769
  else
    n

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickLongInRange (rng : StdGen) : Int × StdGen :=
  pickFromPool longInRangePool rng

private def pickLongOverflow (rng : StdGen) : Int × StdGen :=
  pickFromPool longOverflowPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyPushLong (n : Int) : String :=
  if intFitsSigned257 n then
    if n = maxInt257 ∨ n = minInt257 ∨ n = maxInt257 - 1 ∨ n = minInt257 + 1 then
      "ok-boundary-257"
    else if n = 32768 ∨ n = -32769 ∨ n = 65536 ∨ n = -65536 then
      "ok-boundary-long"
    else
      "ok-long"
  else
    "intov-out-of-range"

private def genPushintLongFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (case0, rng2) :=
    if shape = 0 then
      let (n, r2) := pickLongInRange rng1
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/empty-stack" n, r2)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let n := forceLongImmediate x
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/forced-long-random" n, r2)
    else if shape = 2 then
      let (n, r2) := pickLongInRange rng1
      let (below, r3) := pickSigned257ish r2
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/below-int-preserved" n #[intV below], r3)
    else if shape = 3 then
      let (n, r2) := pickLongInRange rng1
      let (below, r3) := pickNonInt r2
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/below-non-int-preserved" n #[below], r3)
    else if shape = 4 then
      let (n, r2) := pickLongOverflow rng1
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/empty-stack" n, r2)
    else if shape = 5 then
      let (n, r2) := pickLongOverflow rng1
      let (below, r3) := pickSigned257ish r2
      let kind := classifyPushLong n
      (mkPushLongCase s!"fuzz/shape-{shape}/{kind}/with-below-int" n #[intV below], r3)
    else if shape = 6 then
      let (n, r2) := pickLongInRange rng1
      (mkPreludePushLongCase s!"fuzz/shape-{shape}/prelude/nan-before-target" #[.nan] n, r2)
    else if shape = 7 then
      let (ov, r2) := pickLongOverflow rng1
      let (n, r3) := pickLongInRange r2
      (mkPreludePushLongCase s!"fuzz/shape-{shape}/error-order/prelude-range-before-target"
        #[.num ov] n, r3)
    else if shape = 8 then
      let (below1, r2) := pickSigned257ish rng1
      let (below2, r3) := pickSigned257ish r2
      let (n, r4) := pickLongInRange r3
      (mkPreludePushLongCase s!"fuzz/shape-{shape}/prelude/serializable-below-uses-init-stack"
        #[.num below1, .num below2] n, r4)
    else if shape = 9 then
      let (n1, r2) := pickLongInRange rng1
      let (n2, r3) := pickLongInRange r2
      (mkCase s!"fuzz/shape-{shape}/ok/program/two-long-pushes" #[] #[mkPushLongInstr n1, mkPushLongInstr n2], r3)
    else if shape = 10 then
      (mkGasCase s!"fuzz/shape-{shape}/gas/exact-cost-succeeds" pushLongSetGasExact, rng1)
    else if shape = 11 then
      (mkGasCase s!"fuzz/shape-{shape}/gas/exact-minus-one-out-of-gas" pushLongSetGasExactMinusOne, rng1)
    else if shape = 12 then
      let (ov, r2) := pickLongOverflow rng1
      let (n, r3) := pickLongInRange r2
      (mkCase s!"fuzz/shape-{shape}/error-order/prelude-overflow-before-target"
        #[] #[mkPushLongInstr ov, mkPushLongInstr n], r3)
    else if shape = 13 then
      let (n, r2) := pickLongInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok/program/long-then-add" #[intV 1] #[mkPushLongInstr n, .add], r2)
    else if shape = 14 then
      let (n, r2) := pickLongInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok/program/long-plus-neg-long-then-add"
        #[] #[mkPushLongInstr n, mkPushLongInstr (-n), .add], r2)
    else
      let (n, r2) := pickLongInRange rng1
      (mkCase s!"fuzz/shape-{shape}/ok/program/triple-long-push"
        #[] #[mkPushLongInstr n, mkPushLongInstr (n + 1), mkPushLongInstr (n - 1)], r2)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := pushintLongId
  unit := #[
    { name := "unit/direct/ok-long-values-and-stack-order"
      run := do
        expectOkStack "ok/32768" (runPushLongDirect 32768 #[]) #[intV 32768]
        expectOkStack "ok/-32769" (runPushLongDirect (-32769) #[]) #[intV (-32769)]
        expectOkStack "ok/maxInt257" (runPushLongDirect maxInt257 #[]) #[intV maxInt257]
        expectOkStack "ok/minInt257" (runPushLongDirect minInt257 #[]) #[intV minInt257]
        expectOkStack "ok/below-null-preserved"
          (runPushLongDirect 65536 #[.null]) #[.null, intV 65536]
        expectOkStack "ok/below-int-cell-preserved"
          (runPushLongDirect (-65536) #[intV 7, .cell Cell.empty]) #[intV 7, .cell Cell.empty, intV (-65536)] }
    ,
    { name := "unit/direct/intov-overflow-boundaries"
      run := do
        expectErr "overflow/max+1" (runPushLongDirect (maxInt257 + 1) #[]) .intOv
        expectErr "overflow/min-1" (runPushLongDirect (minInt257 - 1) #[]) .intOv
        expectErr "overflow/pow2-257" (runPushLongDirect (pow2 257) #[]) .intOv
        expectErr "overflow/neg-pow2-257" (runPushLongDirect (-(pow2 257)) #[]) .intOv }
    ,
    { name := "unit/opcode/decode-long-boundary-sequence"
      run := do
        let program : Array Instr :=
          #[.pushInt (.num 32767), mkPushLongInstr 32768, mkPushLongInstr (-32769), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/32767-small16" s0 (.pushInt (.num 32767)) 24
        let s2 ← expectDecodeStep "decode/32768-long" s1 (mkPushLongInstr 32768) 13
        let s3 ← expectDecodeStep "decode/-32769-long" s2 (mkPushLongInstr (-32769)) 13
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/opcode/decode-rejects-reserved-len-and-truncated-payload"
      run := do
        let reservedPrefix : Nat := (0x82 <<< 5) + 31
        let reservedCell : Cell := Cell.mkOrdinary (natToBits reservedPrefix 13) #[]
        expectDecodeErr "decode/reserved-len31" (Slice.ofCell reservedCell) .invOpcode

        let len0Prefix : Nat := 0x82 <<< 5
        let truncatedCell : Cell := Cell.mkOrdinary (natToBits len0Prefix 13) #[]
        expectDecodeErr "decode/truncated-payload" (Slice.ofCell truncatedCell) .invOpcode }
    ,
    { name := "unit/opcode/encode-upper-width-and-range-guard"
      run := do
        let wideOk : Int := (pow2 258) - 1
        let code ←
          match assembleCp0 [mkPushLongInstr wideOk] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble wideOk failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/wide-ok-len30" s0 (mkPushLongInstr wideOk) 13
        if s1.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/wide-ok: expected exhausted slice, got {s1.bitsRemaining} bits remaining")

        expectAssembleErr "assemble/too-wide-pos" [mkPushLongInstr (pow2 259)] .rangeChk
        expectAssembleErr "assemble/too-wide-neg" [mkPushLongInstr (-(pow2 259) - 1)] .rangeChk }
    ,
    { name := "unit/dispatch/non-pushint-falls-through"
      run := do
        expectOkStack "fallback/add"
          (runPushLongDispatchFallback .add #[]) #[intV 6060]
        expectOkStack "fallback/pushpow2"
          (runPushLongDispatchFallback (.pushPow2 8) #[]) #[intV 6060] }
  ]
  oracle := #[
    mkPushLongCase "ok/long/pos-32768" 32768,
    mkPushLongCase "ok/long/neg-32769" (-32769),
    mkPushLongCase "ok/long/pos-65536" 65536,
    mkPushLongCase "ok/long/neg-65536" (-65536),
    mkPushLongCase "ok/long/max-int257" maxInt257,
    mkPushLongCase "ok/long/min-int257" minInt257,
    mkPushLongCase "ok/long/max-minus-one" (maxInt257 - 1),
    mkPushLongCase "ok/long/min-plus-one" (minInt257 + 1),
    mkPushLongCase "ok/stack/below-null-preserved" 32768 #[.null],
    mkPushLongCase "ok/stack/below-cell-preserved" (-32769) #[.cell Cell.empty],
    mkPushLongCase "ok/stack/below-int-and-null-preserved" (pow2 40) #[intV 17, .null],
    mkCase "ok/program/two-long-pushes" #[] #[mkPushLongInstr 32768, mkPushLongInstr (-32769)],
    mkPushLongCase "overflow/max-plus-one" (maxInt257 + 1),
    mkPushLongCase "overflow/min-minus-one" (minInt257 - 1),
    mkPushLongCase "overflow/pow2-257" (pow2 257),
    mkPushLongCase "overflow/neg-pow2-257" (-(pow2 257)),
    mkPushLongCase "overflow/len30-upper-value" ((pow2 258) - 1),
    mkPreludePushLongCase "prelude/nan-before-long" #[.nan] 32768,
    mkPreludePushLongCase "prelude/range-high-before-long" #[.num (maxInt257 + 1)] 32768,
    mkPreludePushLongCase "prelude/range-low-before-long" #[.num (minInt257 - 1)] (-32769),
    mkPreludePushLongCase "prelude/serializable-below-values-use-init-stack" #[.num 7, .num (-8)] (pow2 40),
    mkPreludePushLongCase "prelude/mixed-nan-and-finite-below" #[.num 7, .nan] 32768,
    mkCase "error-order/prelude-overflow-before-target-even-with-existing-stack"
      #[.null] #[.pushInt (.num (pow2 257)), mkPushLongInstr 32768],
    mkGasCase "gas/exact-cost-succeeds" pushLongSetGasExact,
    mkGasCase "gas/exact-minus-one-out-of-gas" pushLongSetGasExactMinusOne
  ]
  fuzz := #[
    { seed := 2026020834
      count := 700
      gen := genPushintLongFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHINT_LONG
