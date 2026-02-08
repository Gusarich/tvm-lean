import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QADDRSHIFTMOD

/-
QADDRSHIFTMOD branch-mapping notes (Lean + C++ reference):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shrMod false true 3 (-1) true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popNatUpTo 256`, `popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (quiet decode path `0xb7a920..0xb7a922`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, quiet registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_smallint_range`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QADDRSHIFTMOD specialization):
- Lean: ~9 branch sites / ~15 terminal outcomes
  (dispatch/fallback; depth precheck; shift pop type/range/ok; `w`/`x` pop type gates;
   floor round-mode path; numeric-vs-NaN operand split; fixed `d=3` dual push; quiet fit→NaN).
- C++: ~8 branch sites / ~14 aligned terminal outcomes
  (underflow guard; runtime shift type/range gate; add-path pop order; `y=0` floor rewrite;
   add quotient/remainder path; quiet NaN/overflow push behavior).

Key risk areas covered:
- floor quotient/remainder invariants across sign combinations and boundary shifts;
- strict runtime shift validation (`0..256`) even in quiet mode;
- pop/error ordering (`stkUnd` before type/range; shift before `w`; `w` before `x`);
- quiet NaN funnel for `x`/`w` plus quiet overflow-at-shift-zero behavior (`q=NaN`, `r=0`);
- oracle serialization constraints: NaN and out-of-range ints injected via program prelude;
- deterministic gas cliff for `PUSHINT n; SETGASLIMIT; QADDRSHIFTMOD`.
-/

private def qaddrshiftmodId : InstrId := { name := "QADDRSHIFTMOD" }

private def qaddrshiftmodInstr : Instr :=
  .arithExt (.shrMod false true 3 (-1) true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qaddrshiftmodInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qaddrshiftmodId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseFromIntVals
    (name : String)
    (vals : Array IntVal)
    (programSuffix : Array Instr := #[qaddrshiftmodInstr])
    (below : Array Value := #[])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name (below ++ stack) (progPrefix ++ programSuffix) gasLimits fuel

private def runQAddrShiftModDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qaddrshiftmodInstr stack

private def runQAddrShiftModDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 7341)) stack

private def qaddrshiftmodSetGasExact : Int :=
  computeExactGasBudget qaddrshiftmodInstr

private def qaddrshiftmodSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qaddrshiftmodInstr

private def mkShiftInjectedCase (name : String) (x w : Int) (shift : IntVal) : OracleCase :=
  mkCase name #[intV x, intV w] #[.pushInt shift, qaddrshiftmodInstr]

private def mkXNanInjectedCase (name : String) (w shift : Int) : OracleCase :=
  mkCase name #[intV w, intV shift]
    #[.pushInt .nan, .xchg0 2, .xchg0 1, qaddrshiftmodInstr]

private def mkWNanInjectedCase (name : String) (x shift : Int) : OracleCase :=
  mkCase name #[intV x, intV shift]
    #[.pushInt .nan, .xchg0 1, qaddrshiftmodInstr]

private def shiftBoundaryPool : Array Int :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def shiftInvalidPool : Array Int :=
  #[-3, -2, -1, 257, 258, 300]

private def smallSignedPool : Array Int :=
  #[-33, -17, -9, -7, -5, -3, -1, 0, 1, 3, 5, 7, 9, 17, 33]

private def pickFromPool {α} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftBoundaryPool rng

private def pickShiftValid (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 4
  if mode = 0 then
    pickShiftBoundary rng1
  else
    let (shift, rng2) := randNat rng1 0 256
    (Int.ofNat shift, rng2)

private def pickShiftInvalid (rng : StdGen) : Int × StdGen :=
  pickFromPool shiftInvalidPool rng

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def genQAddrShiftModFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 20
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftBoundary r3
      (mkCase s!"fuzz/shape-{shape}/ok/boundary-triplet" #[intV x, intV w, intV shift], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkCase s!"fuzz/shape-{shape}/ok/signed-mix" #[intV x, intV w, intV shift], r4)
    else if shape = 2 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkCase s!"fuzz/shape-{shape}/ok/x-boundary" #[intV x, intV w, intV shift], r4)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickInt257Boundary r2
      let (shift, r4) := pickShiftValid r3
      (mkCase s!"fuzz/shape-{shape}/ok/w-boundary" #[intV x, intV w, intV shift], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool smallSignedPool rng1
      let (w, r3) := pickFromPool smallSignedPool r2
      let (shift, r4) := pickFromPool #[0, 1, 2, 3, 4, 5, 6, 7, 8] r3
      (mkCase s!"fuzz/shape-{shape}/ok/small-signed" #[intV x, intV w, intV shift], r4)
    else if shape = 5 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-max-plus-one-shift-zero"
        #[intV maxInt257, intV 1, intV 0], rng1)
    else if shape = 6 then
      (mkCase s!"fuzz/shape-{shape}/quiet/overflow-min-minus-one-shift-zero"
        #[intV minInt257, intV (-1), intV 0], rng1)
    else if shape = 7 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftInvalid r3
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range/invalid-shift-via-program" x w (.num shift), r4)
    else if shape = 8 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkShiftInjectedCase s!"fuzz/shape-{shape}/range/shift-nan-via-program" x w .nan, r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/shift-non-int" #[intV x, intV w, nonInt], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValid r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/w-non-int" #[intV x, nonInt, intV shift], r4)
    else if shape = 11 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValid r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/x-non-int" #[nonInt, intV w, intV shift], r4)
    else if shape = 12 then
      let (pick, r2) := randNat rng1 0 2
      let stack :=
        if pick = 0 then
          #[]
        else if pick = 1 then
          #[intV 1]
        else
          #[intV 1, intV 2]
      (mkCase s!"fuzz/shape-{shape}/underflow" stack, r2)
    else if shape = 13 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValid r2
      (mkWNanInjectedCase s!"fuzz/shape-{shape}/quiet/nan-w-via-program" x shift, r3)
    else if shape = 14 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftValid r2
      (mkXNanInjectedCase s!"fuzz/shape-{shape}/quiet/nan-x-via-program" w shift, r3)
    else if shape = 15 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-w-type-via-program"
        #[intV 1, .null] #[.pushInt (.num 300), qaddrshiftmodInstr], rng1)
    else if shape = 16 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-x-type-via-program"
        #[.null, intV 1] #[.pushInt (.num 300), qaddrshiftmodInstr], rng1)
    else if shape = 17 then
      let (xOut, r2) := pickInt257OutOfRange rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftValid r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num xOut, .num w, .num shift], r4)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (wOut, r3) := pickInt257OutOfRange r2
      let (shift, r4) := pickShiftValid r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[.num x, .num wOut, .num shift], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shiftOut, r4) := pickInt257OutOfRange r3
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x, .num w, .num shiftOut], r4)
    else
      (mkCaseFromIntVals s!"fuzz/shape-{shape}/quiet/nan-both-via-program"
        #[.nan, .nan, .num 1], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qaddrshiftmodId
  unit := #[
    { name := "unit/ok/floor-sign-and-remainder-invariants"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 5, 2, 3, 0),
            (-7, 1, 2, -2, 2),
            (7, -8, 2, -1, 3),
            (-7, -1, 2, -2, 0),
            (1, -2, 1, -1, 1),
            (-1, 2, 1, 0, 1),
            (9, -9, 5, 0, 0),
            (5, 3, 0, 8, 0),
            (-5, -3, 0, -8, 0),
            (0, 0, 9, 0, 0)
          ]
        for c in checks do
          let (x, w, shift, q, r) := c
          expectOkStack s!"unit/ok/x={x}/w={w}/shift={shift}"
            (runQAddrShiftModDirect #[intV x, intV w, intV shift]) #[intV q, intV r]
        expectOkStack "unit/ok/below-null-preserved"
          (runQAddrShiftModDirect #[.null, intV 7, intV 5, intV 2])
          #[.null, intV 3, intV 0]
        expectOkStack "unit/ok/below-cell-preserved"
          (runQAddrShiftModDirect #[.cell Cell.empty, intV (-7), intV 1, intV 2])
          #[.cell Cell.empty, intV (-2), intV 2] }
    ,
    { name := "unit/ok/boundary-shifts-and-extremes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 0, maxInt257, 0),
            (minInt257, 0, 0, minInt257, 0),
            (maxInt257, -1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 0, minInt257 + 1, 0),
            (maxInt257, maxInt257, 256, 1, (pow2 256) - 2),
            (minInt257, minInt257, 256, -2, 0),
            (minInt257, 1, 256, -1, 1),
            (maxInt257, -1, 256, 0, (pow2 256) - 2),
            (maxInt257, minInt257, 1, -1, 1)
          ]
        for c in checks do
          let (x, w, shift, q, r) := c
          expectOkStack s!"unit/ok/boundary/x={x}/w={w}/shift={shift}"
            (runQAddrShiftModDirect #[intV x, intV w, intV shift]) #[intV q, intV r] }
    ,
    { name := "unit/quiet/nan-and-shift-zero-overflow-funnel"
      run := do
        expectOkStack "unit/quiet/overflow-max-plus-one-shift-zero"
          (runQAddrShiftModDirect #[intV maxInt257, intV 1, intV 0])
          #[.int .nan, intV 0]
        expectOkStack "unit/quiet/overflow-min-minus-one-shift-zero"
          (runQAddrShiftModDirect #[intV minInt257, intV (-1), intV 0])
          #[.int .nan, intV 0]
        expectOkStack "unit/quiet/nan-w"
          (runQAddrShiftModDirect #[intV 5, .int .nan, intV 4])
          #[.int .nan, .int .nan]
        expectOkStack "unit/quiet/nan-x"
          (runQAddrShiftModDirect #[.int .nan, intV 5, intV 4])
          #[.int .nan, .int .nan] }
    ,
    { name := "unit/error-order/underflow-type-and-range-precedence"
      run := do
        expectErr "unit/error/underflow-empty" (runQAddrShiftModDirect #[]) .stkUnd
        expectErr "unit/error/underflow-one-arg" (runQAddrShiftModDirect #[intV 1]) .stkUnd
        expectErr "unit/error/underflow-two-args" (runQAddrShiftModDirect #[intV 1, intV 2]) .stkUnd
        expectErr "unit/error/underflow-before-type-with-two-items"
          (runQAddrShiftModDirect #[.null, intV 2]) .stkUnd
        expectErr "unit/error/type-shift-first-null"
          (runQAddrShiftModDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "unit/error/type-shift-first-cell"
          (runQAddrShiftModDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "unit/error/type-w-second"
          (runQAddrShiftModDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "unit/error/type-x-third"
          (runQAddrShiftModDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "unit/error/range-shift-negative"
          (runQAddrShiftModDirect #[intV 7, intV 5, intV (-1)]) .rangeChk
        expectErr "unit/error/range-shift-over256"
          (runQAddrShiftModDirect #[intV 7, intV 5, intV 257]) .rangeChk
        expectErr "unit/error/range-shift-nan"
          (runQAddrShiftModDirect #[intV 7, intV 5, .int .nan]) .rangeChk
        expectErr "unit/error/order-range-before-w-type"
          (runQAddrShiftModDirect #[intV 1, .null, intV 257]) .rangeChk
        expectErr "unit/error/order-range-before-x-type"
          (runQAddrShiftModDirect #[.null, intV 1, intV 257]) .rangeChk }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "unit/dispatch/fallback"
          (runQAddrShiftModDispatchFallback #[]) #[intV 7341] }
  ]
  oracle := #[
    mkCase "ok/floor/basic-pos-pos" #[intV 7, intV 5, intV 2],
    mkCase "ok/floor/basic-neg-pos" #[intV (-7), intV 1, intV 2],
    mkCase "ok/floor/basic-pos-neg" #[intV 7, intV (-8), intV 2],
    mkCase "ok/floor/basic-neg-neg" #[intV (-7), intV (-1), intV 2],
    mkCase "ok/floor/shift-zero-pos" #[intV 5, intV 3, intV 0],
    mkCase "ok/floor/shift-zero-neg" #[intV (-5), intV (-3), intV 0],
    mkCase "ok/floor/shift-one-mixed-a" #[intV 1, intV (-2), intV 1],
    mkCase "ok/floor/shift-one-mixed-b" #[intV (-1), intV 2, intV 1],
    mkCase "ok/floor/canceling-sum" #[intV 9, intV (-9), intV 5],
    mkCase "ok/boundary/max-plus-zero-shift-zero" #[intV maxInt257, intV 0, intV 0],
    mkCase "ok/boundary/min-plus-zero-shift-zero" #[intV minInt257, intV 0, intV 0],
    mkCase "ok/boundary/max-plus-neg-one-shift-zero" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/boundary/min-plus-one-shift-zero" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-plus-max-shift-256" #[intV maxInt257, intV maxInt257, intV 256],
    mkCase "ok/boundary/min-plus-min-shift-256" #[intV minInt257, intV minInt257, intV 256],
    mkCase "ok/boundary/min-plus-one-shift-256" #[intV minInt257, intV 1, intV 256],
    mkCase "ok/boundary/max-plus-neg-one-shift-256" #[intV maxInt257, intV (-1), intV 256],
    mkCase "ok/boundary/max-plus-min-shift-one" #[intV maxInt257, intV minInt257, intV 1],
    mkCase "quiet/overflow/max-plus-one-shift-zero" #[intV maxInt257, intV 1, intV 0],
    mkCase "quiet/overflow/min-minus-one-shift-zero" #[intV minInt257, intV (-1), intV 0],
    mkShiftInjectedCase "range/shift-negative-via-program" 7 5 (.num (-1)),
    mkShiftInjectedCase "range/shift-over256-via-program" 7 5 (.num 257),
    mkShiftInjectedCase "range/shift-nan-via-program" 7 5 .nan,
    mkWNanInjectedCase "quiet/nan-w-via-program" 5 4,
    mkXNanInjectedCase "quiet/nan-x-via-program" 5 4,
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-type-two-items" #[.null, intV 2],
    mkCase "type/pop-shift-first-null" #[intV 1, intV 2, .null],
    mkCase "type/pop-shift-first-cell" #[intV 1, intV 2, .cell Cell.empty],
    mkCase "type/pop-w-second-null" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third-null" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-w-when-both-non-int"
      #[intV 1, .cell Cell.empty, .null],
    mkCase "error-order/pop-w-before-x-when-shift-int"
      #[.null, .cell Cell.empty, intV 1],
    mkCase "error-order/range-before-w-type-via-program" #[intV 1, .null]
      #[.pushInt (.num 300), qaddrshiftmodInstr],
    mkCase "error-order/range-before-x-type-via-program" #[.null, intV 1]
      #[.pushInt (.num 300), qaddrshiftmodInstr],
    mkCaseFromIntVals "error-order/pushint-overflow-x-high-before-op"
      #[.num (maxInt257 + 1), .num 7, .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-x-low-before-op"
      #[.num (minInt257 - 1), .num 7, .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-w-high-before-op"
      #[.num 7, .num (maxInt257 + 1), .num 3],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-high-before-op"
      #[.num 7, .num 5, .num (maxInt257 + 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-shift-low-before-op"
      #[.num 7, .num 5, .num (minInt257 - 1)],
    mkCaseFromIntVals "error-order/pushint-overflow-all-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num (pow2 257)],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num qaddrshiftmodSetGasExact), .tonEnvOp .setGasLimit, qaddrshiftmodInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num qaddrshiftmodSetGasExactMinusOne), .tonEnvOp .setGasLimit, qaddrshiftmodInstr]
  ]
  fuzz := #[
    { seed := 2026020841
      count := 700
      gen := genQAddrShiftModFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QADDRSHIFTMOD
