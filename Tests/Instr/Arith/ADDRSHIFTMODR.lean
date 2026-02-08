import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.ADDRSHIFTMODR

/-
ADDRSHIFTMODR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean` (`execInstrArithExt`, `.shrMod`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (CP0 encoding for SHR/MOD family)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (decode range `0xa920..0xa922`)
- C++ analyzed file:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shrmod`, opcode wiring in `register_div_ops`).

Branch counts used for this suite (instruction-fixed path:
`mul=false`, `add=true`, `d=3`, `roundMode=0`, `quiet=false`, `zOpt=none`):
- Lean: 8 branch sites / 11 terminal outcomes
  (dispatch; pre-underflow check; shift pop success/type/range;
   `x/w` numeric split; round-mode guard; `d` switch; two `pushIntQuiet` checks).
- C++: 7 branch sites / 11 aligned outcomes
  (`check_underflow(3)`; `pop_smallint_range(256)`; `y==0` round rewrite;
   `pop_int` type checks for `w` then `x`; add path; two `push_int_quiet` checks).

Key risk areas covered:
- operand pop order is `shift`, then `w`, then `x` (error ordering sensitive);
- underflow must dominate malformed shift when depth < 3;
- non-quiet NaN propagation must throw `intOv`;
- runtime shift range is strict `[0, 256]` (`rangeChk` otherwise);
- zero-shift runtime form rewrites round mode to floor (`-1`);
- signed-257 overflow in `x + w` must fail before remainder push;
- gas boundary determinism for `PUSHINT n; SETGASLIMIT; ADDRSHIFTMODR`.
-/

private def addrShiftModRId : InstrId := { name := "ADDRSHIFTMODR" }

private def addrShiftModRInstr : Instr :=
  .arithExt (.shrMod false true 3 0 false none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[addrShiftModRInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := addrShiftModRId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runAddrShiftModRDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt addrShiftModRInstr stack

private def addrShiftModRSetGasExact : Int :=
  computeExactGasBudget addrShiftModRInstr

private def addrShiftModRSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne addrShiftModRInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 7, 8, 31, 32, 63, 64, 127, 128, 255, 256]

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickShiftBoundary rng1
  else
    randNat rng1 0 256

private def genAddrShiftModRFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 6
  let ((x, w, shift), rng2) :=
    if shape = 0 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickInt257Boundary r2
      let (s0, r4) := pickShiftBoundary r3
      ((x0, w0, s0), r4)
    else if shape = 1 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickSigned257ish r2
      let (s0, r4) := pickShiftMixed r3
      ((x0, w0, s0), r4)
    else if shape = 2 then
      let (x0, r2) := pickInt257Boundary rng1
      let (w0, r3) := pickSigned257ish r2
      let (s0, r4) := pickShiftMixed r3
      ((x0, w0, s0), r4)
    else if shape = 3 then
      let (x0, r2) := pickSigned257ish rng1
      let (w0, r3) := pickInt257Boundary r2
      let (s0, r4) := pickShiftMixed r3
      ((x0, w0, s0), r4)
    else if shape = 4 then
      let (x0, r2) := pickSigned257ish rng1
      let (s0, r3) := pickShiftMixed r2
      ((x0, 0, s0), r3)
    else if shape = 5 then
      let (w0, r2) := pickSigned257ish rng1
      let (s0, r3) := pickShiftMixed r2
      ((0, w0, s0), r3)
    else
      let (useMax, r2) := randBool rng1
      let x0 := if useMax then maxInt257 else minInt257
      let w0 := if useMax then 1 else -1
      let (pick, r3) := randNat r2 0 1
      let s0 : Nat := if pick = 0 then 0 else 1
      ((x0, w0, s0), r3)
  let (tag, rng3) := randNat rng2 0 999_999
  (mkCase s!"fuzz/shape-{shape}-{tag}" #[intV x, intV w, intV (Int.ofNat shift)], rng3)

def suite : InstrSuite where
  id := addrShiftModRId
  unit := #[
    { name := "unit/direct/success-basic-boundary-and-stack-shape"
      run := do
        expectOkStack "zero/shift0" (runAddrShiftModRDirect #[intV 0, intV 0, intV 0]) #[intV 0, intV 0]
        expectOkStack "even/shift1" (runAddrShiftModRDirect #[intV 21, intV 11, intV 1]) #[intV 16, intV 0]
        expectOkStack "neg-even/shift2" (runAddrShiftModRDirect #[intV (-21), intV 5, intV 2]) #[intV (-4), intV 0]
        expectOkStack "max-1/shift0" (runAddrShiftModRDirect #[intV maxInt257, intV (-1), intV 0])
          #[intV (maxInt257 - 1), intV 0]
        expectOkStack "min+1/shift0" (runAddrShiftModRDirect #[intV minInt257, intV 1, intV 0])
          #[intV (minInt257 + 1), intV 0]
        expectOkStack "lower-stack-preserved"
          (runAddrShiftModRDirect #[.null, intV 21, intV 11, intV 1])
          #[.null, intV 16, intV 0] }
    ,
    { name := "unit/direct/intov-from-overflow-and-nan-operands"
      run := do
        expectErr "max+1/shift0" (runAddrShiftModRDirect #[intV maxInt257, intV 1, intV 0]) .intOv
        expectErr "min-1/shift0" (runAddrShiftModRDirect #[intV minInt257, intV (-1), intV 0]) .intOv
        expectErr "w-nan" (runAddrShiftModRDirect #[intV 5, .int .nan, intV 1]) .intOv
        expectErr "x-nan" (runAddrShiftModRDirect #[.int .nan, intV 5, intV 1]) .intOv }
    ,
    { name := "unit/direct/error-ordering-shift-pop-and-operand-type"
      run := do
        expectErr "underflow/empty" (runAddrShiftModRDirect #[]) .stkUnd
        expectErr "underflow/one" (runAddrShiftModRDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-with-bad-shift" (runAddrShiftModRDirect #[intV 1, .null]) .stkUnd
        expectErr "type/shift-top-null" (runAddrShiftModRDirect #[intV 5, intV 6, .null]) .typeChk
        expectErr "range/shift-top-nan" (runAddrShiftModRDirect #[intV 5, intV 6, .int .nan]) .rangeChk
        expectErr "type/w-second-null" (runAddrShiftModRDirect #[intV 5, .null, intV 1]) .typeChk
        expectErr "type/x-third-null" (runAddrShiftModRDirect #[.null, intV 6, intV 1]) .typeChk }
    ,
    { name := "unit/opcode/encode-decode-roundtrip"
      run := do
        let code ←
          match assembleCp0 [addrShiftModRInstr] with
          | .ok c => pure c
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        match decodeCp0WithBits (Slice.ofCell code) with
        | .error e =>
            throw (IO.userError s!"decode failed: {e}")
        | .ok (instr, bits, _) =>
            if instr != addrShiftModRInstr then
              throw (IO.userError s!"expected {reprStr addrShiftModRInstr}, got {reprStr instr}")
            else if bits != 16 then
              throw (IO.userError s!"expected 16-bit decode, got {bits}")
            else
              pure () }
  ]
  oracle := #[
    mkCase "ok/shift0-zero-sum" #[intV 0, intV 0, intV 0],
    mkCase "ok/shift1-even-positive" #[intV 21, intV 11, intV 1],
    mkCase "ok/shift2-even-negative" #[intV (-21), intV 5, intV 2],
    mkCase "ok/shift0-max-minus-one" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/shift0-min-plus-one" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/shift0-max-plus-min" #[intV maxInt257, intV minInt257, intV 0],
    mkCase "ok/rounding/nonzero-remainder-pos" #[intV 7, intV 2, intV 2],
    mkCase "ok/rounding/nonzero-remainder-neg" #[intV (-7), intV 2, intV 2],
    mkCase "ok/shift256-zero-input" #[intV 0, intV 0, intV 256],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-item" #[intV 1],
    mkCase "underflow/two-items" #[intV 1, intV 2],
    mkCase "error-order/underflow-before-shift-type-two-items" #[intV 9, .null],
    mkCase "error-order/underflow-before-shift-range-two-items" #[intV 9]
      #[.pushInt (.num 257), addrShiftModRInstr],
    mkCase "error-order/shift-type-before-w-type" #[intV 9, .null, .null],
    mkCase "error-order/w-type-before-x-type" #[.null, .null, intV 1],
    mkCase "type/shift-top-null-full" #[intV 5, intV 6, .null],
    mkCase "type/shift-top-cell-full" #[intV 5, intV 6, .cell Cell.empty],
    mkCase "type/w-second-null" #[intV 5, .null, intV 1],
    mkCase "type/x-third-null" #[.null, intV 6, intV 1],
    mkCase "range/shift-negative-program" #[intV 5, intV 6]
      #[.pushInt (.num (-1)), addrShiftModRInstr],
    mkCase "range/shift-too-large-program" #[intV 5, intV 6]
      #[.pushInt (.num 257), addrShiftModRInstr],
    mkCase "range/shift-nan-program" #[intV 5, intV 6]
      #[.pushInt .nan, addrShiftModRInstr],
    mkCase "intov/overflow-max-plus-one-shift0" #[intV maxInt257, intV 1, intV 0],
    mkCase "intov/overflow-min-minus-one-shift0" #[intV minInt257, intV (-1), intV 0],
    mkCase "intov/w-nan-program" #[intV 5]
      #[.pushInt .nan, .pushInt (.num 1), addrShiftModRInstr],
    mkCase "intov/x-nan-program" #[intV 5]
      #[.pushInt .nan, .xchg0 1, .pushInt (.num 1), addrShiftModRInstr],
    mkCase "gas/exact-cost-succeeds" #[intV 21, intV 11, intV 1]
      #[.pushInt (.num addrShiftModRSetGasExact), .tonEnvOp .setGasLimit, addrShiftModRInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 21, intV 11, intV 1]
      #[.pushInt (.num addrShiftModRSetGasExactMinusOne), .tonEnvOp .setGasLimit, addrShiftModRInstr]
  ]
  fuzz := #[
    { seed := 2026020803
      count := 600
      gen := genAddrShiftModRFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMODR
