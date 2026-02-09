import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QMULMODPOW2

/-
QMULMODPOW2 branch-map notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.arithExt (.shrMod true false 2 (-1) true none)` path)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (quiet `shrMod` runtime-shift encoding as `0xb7 ++ 0xa9a8..0xa9aa`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode family `0xb7a9a8..0xb7a9aa` -> `QMULMODPOW2{,R,C}`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_mulshrmod`, `dump_mulshrmod`, registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch / terminal counts used for this suite:
- Lean generic `.shrMod` helper: 9 branch sites / 20 terminal outcomes.
- Lean specialization (`mul=true`, `add=false`, `d=2`, `round=-1`, `quiet=true`,
  runtime shift): 7 branch sites / 8 reachable terminal outcomes
  (finite success; quiet-NaN from bad shift; quiet-NaN from non-finite operand;
   `stkUnd`; shift `typeChk`; `y` `typeChk`; `x` `typeChk`; dispatch fallthrough).
- C++ quiet runtime `exec_mulshrmod` path: 8 branch sites / 12 aligned outcomes
  (underflow gate, shift parse/range class, operand pop order gates, quiet NaN funnel,
   opcode mode/decode split, and push shape).

Key risk areas covered:
- floor modulo semantics across sign combinations and shift boundaries (`0..256`);
- quiet bad-shift behavior (`z<0`, `z>256`, `z=NaN`) => pushed NaN, not `rangeChk`;
- pop/error ordering (`z` first, then `y`, then `x`) including bad-shift precedence;
- quiet NaN funnels for `x`/`y` NaN without using raw-NaN oracle init stacks;
- oracle/fuzz serialization discipline: NaN and signed-257 out-of-range values are
  injected via `PUSHINT` prelude helpers only;
- exact gas cliff for `PUSHINT n; SETGASLIMIT; QMULMODPOW2`.
-/

private def qmulmodpow2Id : InstrId := { name := "QMULMODPOW2" }

private def qmulmodpow2Instr : Instr :=
  .arithExt (.shrMod true false 2 (-1) true none)

private def mulmodpow2Instr : Instr :=
  .arithExt (.shrMod true false 2 (-1) false none)

private def slashCaseName (name : String) : String :=
  if name.startsWith "/" then name else s!"/{name}"

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qmulmodpow2Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := slashCaseName name
    instr := qmulmodpow2Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qmulmodpow2Instr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def mkShiftInjectedCase (name : String) (x y : Value) (shift : IntVal) : OracleCase :=
  mkCase name #[x, y] #[.pushInt shift, qmulmodpow2Instr]

private def mkYNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift] #[.pushInt .nan, .xchg0 1, qmulmodpow2Instr]

private def mkXNanInjectedCase (name : String) (y shift : Int) : OracleCase :=
  mkCase name #[intV y, intV shift] #[.pushInt .nan, .xchg0 2, .xchg0 1, qmulmodpow2Instr]

private def runQmulmodpow2Direct (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qmulmodpow2Instr stack

private def runQmulmodpow2DispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 5296)) stack

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

private def qmulmodpow2SetGasExact : Int :=
  computeExactGasBudget qmulmodpow2Instr

private def qmulmodpow2SetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qmulmodpow2Instr

private def validShiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def invalidShiftPool : Array Int :=
  #[-4, -3, -2, -1, 257, 258, 300, 511]

private def smallFactorPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickValidShift (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 6
  if mode = 0 then
    pickFromPool validShiftBoundaryPool rng1
  else
    let (z, rng2) := randNat rng1 0 256
    (Int.ofNat z, rng2)

private def pickInvalidShift (rng : StdGen) : Int × StdGen :=
  pickFromPool invalidShiftPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (isNull, rng') := randBool rng
  (if isNull then .null else .cell Cell.empty, rng')

private def classifyFiniteModCase (x y : Int) (shift : Nat) : String :=
  let r := modPow2Round (x * y) shift (-1)
  if r = 0 then
    "exact"
  else
    "inexact"

private def genQmulmodpow2FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickFromPool validShiftBoundaryPool r3
      let kind := classifyFiniteModCase x y shift.toNat
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/boundary-triplet"
        #[intV x, intV y, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyFiniteModCase x y shift.toNat
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/signed-triplet"
        #[intV x, intV y, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyFiniteModCase x y shift.toNat
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/x-boundary"
        #[intV x, intV y, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickInt257Boundary r2
      let (shift, r4) := pickValidShift r3
      let kind := classifyFiniteModCase x y shift.toNat
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/y-boundary"
        #[intV x, intV y, intV shift], r4)
    else if shape = 4 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkCase s!"/fuzz/shape-{shape}/quiet/invalid-shift-direct"
        #[intV x, intV y, intV shift], r4)
    else if shape = 5 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickInvalidShift r3
      (mkShiftInjectedCase s!"/fuzz/shape-{shape}/quiet/invalid-shift-via-program"
        (intV x) (intV y) (.num shift), r4)
    else if shape = 6 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV y, shiftLike], r4)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, yLike, intV shift], r4)
    else if shape = 8 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-third"
        #[xLike, intV y, intV shift], r4)
    else if shape = 9 then
      let (variant, r2) := randNat rng1 0 4
      if variant = 0 then
        (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], r2)
      else if variant = 1 then
        let (x, r3) := pickSigned257ish r2
        (mkCase s!"/fuzz/shape-{shape}/underflow/one-int" #[intV x], r3)
      else if variant = 2 then
        let (x, r3) := pickSigned257ish r2
        let (y, r4) := pickSigned257ish r3
        (mkCase s!"/fuzz/shape-{shape}/underflow/two-ints" #[intV x, intV y], r4)
      else if variant = 3 then
        let (x, r3) := pickSigned257ish r2
        (mkCase s!"/fuzz/shape-{shape}/underflow/invalid-shift-injected-before-pop"
          #[intV x] #[.pushInt (.num (-1)), qmulmodpow2Instr], r3)
      else
        let (v, r3) := pickNonInt r2
        (mkCase s!"/fuzz/shape-{shape}/underflow/one-non-int" #[v], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/quiet/nan-shift-via-program"
        #[.num x, .num y, .nan], r3)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkYNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-y-via-program" x shift, r3)
    else if shape = 12 then
      let (y, r2) := pickSigned257ish rng1
      let (shift, r3) := pickValidShift r2
      (mkXNanInjectedCase s!"/fuzz/shape-{shape}/quiet/nan-x-via-program" y shift, r3)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (badShift, r3) := pickInvalidShift r2
      let (yLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-y-type"
        #[intV x, yLike] #[.pushInt (.num badShift), qmulmodpow2Instr], r4)
    else if shape = 14 then
      let (y, r2) := pickSigned257ish rng1
      let (badShift, r3) := pickInvalidShift r2
      let (xLike, r4) := pickNonInt r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-before-x-type"
        #[xLike, intV y] #[.pushInt (.num badShift), qmulmodpow2Instr], r4)
    else if shape = 15 then
      let (xLike, r2) := pickNonInt rng1
      let (yLike, r3) := pickNonInt r2
      let (shift, r4) := pickValidShift r3
      (mkCase s!"/fuzz/shape-{shape}/error-order/pop-y-before-x-both-non-int"
        #[xLike, yLike, intV shift], r4)
    else if shape = 16 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (y, r3) := pickSigned257ish r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num xOut, .num y, .num shift], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[.num x, .num yOut, .num shift], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x, .num y, .num shiftOut], r4)
    else if shape = 19 then
      let (x, r2) := pickFromPool smallFactorPool rng1
      let (y, r3) := pickFromPool smallFactorPool r2
      let (shift, r4) := pickFromPool (#[0, 1, 2, 3, 4, 5, 6, 7, 8] : Array Int) r3
      let kind := classifyFiniteModCase x y shift.toNat
      (mkCase s!"/fuzz/shape-{shape}/ok/{kind}/small-sign-mix"
        #[intV x, intV y, intV shift], r4)
    else
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (yOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickValidShift r3
      (mkCaseFromIntVals s!"/fuzz/shape-{shape}/error-order/pushint-overflow-both-operands-before-op"
        #[.num xOut, .num yOut, .num shift], r4)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qmulmodpow2Id
  unit := #[
    { name := "/unit/direct/floor-modpow2-sign-zero-and-shift-boundary-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int) :=
          #[
            (0, 0, 0, 0),
            (7, 3, 0, 0),
            (-7, 3, 0, 0),
            (7, 3, 2, 1),
            (-7, 3, 2, 3),
            (7, -3, 2, 3),
            (-7, -3, 2, 1),
            (13, 11, 4, 15),
            (-13, 11, 4, 1),
            (13, -11, 4, 1),
            (-13, -11, 4, 15),
            (5, 0, 7, 0),
            (0, 5, 7, 0),
            (maxInt257, 1, 1, 1),
            (maxInt257, 1, 255, (pow2 255) - 1),
            (maxInt257, 1, 256, maxInt257),
            (minInt257, 1, 1, 0),
            (minInt257, -1, 1, 0),
            (minInt257, 1, 255, 0),
            (minInt257, 1, 256, 0),
            (minInt257 + 1, 1, 256, 1),
            (minInt257 + 1, -1, 256, maxInt257),
            (-1, 1, 256, maxInt257)
          ]
        for c in checks do
          match c with
          | (x, y, shift, expected) =>
              expectOkStack s!"/unit/check/({x}*{y})%2^{shift}"
                (runQmulmodpow2Direct #[intV x, intV y, intV shift]) #[intV expected]
        expectOkStack "/unit/order/below-stack-preserved"
          (runQmulmodpow2Direct #[.null, intV 13, intV 11, intV 4]) #[.null, intV 15] }
    ,
    { name := "/unit/direct/quiet-invalid-shift-and-nan-funnels"
      run := do
        expectOkStack "/unit/quiet/shift-negative-to-nan"
          (runQmulmodpow2Direct #[intV 7, intV 5, intV (-1)]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-overmax-to-nan"
          (runQmulmodpow2Direct #[intV 7, intV 5, intV 257]) #[.int .nan]
        expectOkStack "/unit/quiet/shift-nan-to-nan"
          (runQmulmodpow2Direct #[intV 7, intV 5, .int .nan]) #[.int .nan]
        expectOkStack "/unit/quiet/y-nan-to-nan"
          (runQmulmodpow2Direct #[intV 7, .int .nan, intV 1]) #[.int .nan]
        expectOkStack "/unit/quiet/x-nan-to-nan"
          (runQmulmodpow2Direct #[.int .nan, intV 7, intV 1]) #[.int .nan]
        expectOkStack "/unit/quiet/invalid-shift-with-finite-operands-still-nan"
          (runQmulmodpow2Direct #[intV (-9), intV 4, intV 300]) #[.int .nan] }
    ,
    { name := "/unit/error-order/underflow-type-and-pop-order"
      run := do
        expectErr "/unit/error/underflow-empty" (runQmulmodpow2Direct #[]) .stkUnd
        expectErr "/unit/error/underflow-one-item" (runQmulmodpow2Direct #[intV 1]) .stkUnd
        expectErr "/unit/error/underflow-two-items" (runQmulmodpow2Direct #[intV 1, intV 2]) .stkUnd
        expectErr "/unit/error/underflow-two-non-int-items"
          (runQmulmodpow2Direct #[.cell Cell.empty, .null]) .stkUnd
        expectErr "/unit/error/type-shift-pop-first-null"
          (runQmulmodpow2Direct #[intV 7, intV 5, .null]) .typeChk
        expectErr "/unit/error/type-shift-pop-first-cell"
          (runQmulmodpow2Direct #[intV 7, intV 5, .cell Cell.empty]) .typeChk
        expectErr "/unit/error/type-y-pop-second"
          (runQmulmodpow2Direct #[intV 7, .null, intV 1]) .typeChk
        expectErr "/unit/error/type-x-pop-third"
          (runQmulmodpow2Direct #[.null, intV 7, intV 1]) .typeChk
        expectErr "/unit/error/order-bad-shift-before-y-type"
          (runQmulmodpow2Direct #[intV 7, .null, intV (-1)]) .typeChk
        expectErr "/unit/error/order-bad-shift-before-x-type"
          (runQmulmodpow2Direct #[.null, intV 7, intV 257]) .typeChk
        expectErr "/unit/error/order-pop-y-before-x-when-both-non-int"
          (runQmulmodpow2Direct #[.null, .cell Cell.empty, intV 1]) .typeChk
        expectErr "/unit/error/order-shift-type-before-y-x"
          (runQmulmodpow2Direct #[.null, .cell Cell.empty, .null]) .typeChk }
    ,
    { name := "/unit/opcode/quiet-vs-nonquiet-decode-boundary"
      run := do
        let program : Array Instr := #[qmulmodpow2Instr, mulmodpow2Instr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/unit/decode/qmulmodpow2" s0 qmulmodpow2Instr 24
        let s2 ← expectDecodeStep "/unit/decode/mulmodpow2" s1 mulmodpow2Instr 16
        let s3 ← expectDecodeStep "/unit/decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/unit/decode/tail-add: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/unit/dispatch/fallback"
          (runQmulmodpow2DispatchFallback #[]) #[intV 5296] }
  ]
  oracle := #[
    mkCase "/ok/shift-zero/zero-product" #[intV 0, intV 7, intV 0],
    mkCase "/ok/shift-zero/pos-pos" #[intV 7, intV 5, intV 0],
    mkCase "/ok/shift-zero/neg-pos" #[intV (-7), intV 5, intV 0],
    mkCase "/ok/shift-zero/pos-neg" #[intV 7, intV (-5), intV 0],
    mkCase "/ok/shift-zero/neg-neg" #[intV (-7), intV (-5), intV 0],
    mkCase "/ok/floor/pos-pos-inexact" #[intV 7, intV 3, intV 2],
    mkCase "/ok/floor/neg-pos-inexact" #[intV (-7), intV 3, intV 2],
    mkCase "/ok/floor/pos-neg-inexact" #[intV 7, intV (-3), intV 2],
    mkCase "/ok/floor/neg-neg-inexact" #[intV (-7), intV (-3), intV 2],
    mkCase "/ok/exact/divisible-pos" #[intV 12, intV 8, intV 5],
    mkCase "/ok/exact/divisible-neg" #[intV (-12), intV 8, intV 5],
    mkCase "/ok/exact/x-zero" #[intV 0, intV 19, intV 7],
    mkCase "/ok/exact/y-zero" #[intV 19, intV 0, intV 7],
    mkCase "/ok/boundary/max-times-one-shift1" #[intV maxInt257, intV 1, intV 1],
    mkCase "/ok/boundary/max-times-one-shift255" #[intV maxInt257, intV 1, intV 255],
    mkCase "/ok/boundary/max-times-one-shift256" #[intV maxInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-times-one-shift1" #[intV minInt257, intV 1, intV 1],
    mkCase "/ok/boundary/min-times-one-shift255" #[intV minInt257, intV 1, intV 255],
    mkCase "/ok/boundary/min-times-one-shift256" #[intV minInt257, intV 1, intV 256],
    mkCase "/ok/boundary/min-plus-one-times-negone-shift256"
      #[intV (minInt257 + 1), intV (-1), intV 256],
    mkCase "/ok/boundary/negone-times-one-shift256" #[intV (-1), intV 1, intV 256],
    mkCase "/ok/order/below-null-preserved" #[.null, intV 13, intV 11, intV 4],
    mkCase "/ok/order/below-cell-preserved" #[.cell Cell.empty, intV (-13), intV 11, intV 4],
    mkCase "/quiet/invalid-shift-negative-direct" #[intV 7, intV 5, intV (-1)],
    mkCase "/quiet/invalid-shift-overmax-direct" #[intV 7, intV 5, intV 257],
    mkShiftInjectedCase "/quiet/invalid-shift-negative-via-program" (intV 7) (intV 5) (.num (-1)),
    mkShiftInjectedCase "/quiet/invalid-shift-overmax-via-program" (intV 7) (intV 5) (.num 257),
    mkCaseFromIntVals "/quiet/nan-shift-via-program" #[.num 7, .num 5, .nan],
    mkYNanInjectedCase "/quiet/nan-y-via-program" 7 1,
    mkXNanInjectedCase "/quiet/nan-x-via-program" 5 1,
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-item" #[intV 1],
    mkCase "/underflow/two-items" #[intV 1, intV 2],
    mkCase "/underflow/two-non-int-items" #[.cell Cell.empty, .null],
    mkCase "/error-order/underflow-before-shift-pop-via-program" #[intV 7]
      #[.pushInt (.num (-1)), qmulmodpow2Instr],
    mkCase "/type/pop-shift-first-null" #[intV 7, intV 5, .null],
    mkCase "/type/pop-shift-first-cell" #[intV 7, intV 5, .cell Cell.empty],
    mkCase "/type/pop-y-second-null" #[intV 7, .null, intV 1],
    mkCase "/type/pop-x-third-null" #[.null, intV 7, intV 1],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int" #[intV 7, .cell Cell.empty, .null],
    mkCase "/error-order/pop-y-before-x-after-valid-shift" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/bad-shift-before-y-type-via-program" #[intV 7, .null]
      #[.pushInt (.num (-1)), qmulmodpow2Instr],
    mkCase "/error-order/bad-shift-before-x-type-via-program" #[.null, intV 7]
      #[.pushInt (.num 257), qmulmodpow2Instr],
    mkCaseFromIntVals "/error-order/pushint-overflow-x-before-op"
      #[.num (pow2 257), .num 7, .num 5],
    mkCaseFromIntVals "/error-order/pushint-overflow-y-before-op"
      #[.num 7, .num (-(pow2 257)), .num 5],
    mkCaseFromIntVals "/error-order/pushint-overflow-shift-before-op"
      #[.num 7, .num 5, .num (pow2 257)],
    mkCaseFromIntVals "/error-order/pushint-overflow-all-before-op"
      #[.num (maxInt257 + 1), .num (minInt257 - 1), .num (pow2 257)],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2SetGasExact), .tonEnvOp .setGasLimit, qmulmodpow2Instr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 3]
      #[.pushInt (.num qmulmodpow2SetGasExactMinusOne), .tonEnvOp .setGasLimit, qmulmodpow2Instr]
  ]
  fuzz := #[
    { seed := 2026020857
      count := 700
      gen := genQmulmodpow2FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODPOW2
