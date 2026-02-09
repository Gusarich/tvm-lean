import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTDIVMODR

/-
QLSHIFTDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 0 false true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest ties toward `+∞`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q family decode: `0xb7a9cc..0xb7a9ce`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, quiet mode registration in `register_div_ops`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)

Branch counts used for this suite (QLSHIFTDIVMODR specialization):
- Lean specialization: ~9 branch sites / ~17 terminal outcomes
  (dispatch/fallback; pre-underflow gate; shift pop/range gate; pop order `shift→y→x`;
   bad-shift NaN funnel; numeric-vs-invalid split; `y=0` NaN branch;
   fixed round-mode validity branch; `d=3` double-push with quiet overflow funnels).
- C++ specialization: ~8 branch sites / ~15 aligned terminal outcomes
  (`check_underflow`; runtime shift parse/range gate; operand validity split;
   divisor-zero path; `mod_div` path; double `push_int_quiet` ordering for `q,r`).

Key risk areas covered:
- nearest rounding ties toward `+∞` and output order (`q` then `r`);
- quiet range behavior (`shift < 0` or `shift > 256`) producing NaNs, not `rangeChk`;
- strict pop/error ordering even on bad shifts (`shift` consumed first, then `y`, then `x`);
- quiet funnels for division-by-zero and NaN operands (two NaNs for `d=3`);
- quotient-overflow behavior in quiet mode (`q` may become NaN while `r` remains numeric);
- oracle-safe NaN/out-of-range injection via program (`PUSHINT ...`) only;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qlshiftDivModrId : InstrId := { name := "QLSHIFTDIVMODR" }

private def qlshiftDivModrInstr : Instr :=
  .arithExt (.shlDivMod 3 0 false true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftDivModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qlshiftDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQlshiftDivModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftDivModrInstr stack

private def runQlshiftDivModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 2167)) stack

private def expectQlshiftDivModr
    (label : String)
    (x y shift q r : Int) : IO Unit :=
  expectOkStack label
    (runQlshiftDivModrDirect #[intV x, intV y, intV shift])
    #[intV q, intV r]

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

private def qlshiftDivModrSetGasExact : Int :=
  computeExactGasBudget qlshiftDivModrInstr

private def qlshiftDivModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftDivModrInstr

private def shiftBoundaryPool : Array Nat :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256]

private def tieNumeratorPool : Array Int :=
  #[-15, -13, -11, -9, -7, -5, -3, -1, 1, 3, 5, 7, 9, 11, 13, 15]

private def tieDivisorPool : Array Int :=
  #[-2, 2]

private def pickFromPool (pool : Array Int) (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickShiftBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (shiftBoundaryPool.size - 1)
  (shiftBoundaryPool[idx]!, rng')

private def pickShiftUniform (rng : StdGen) : Nat × StdGen :=
  randNat rng 0 256

private def pickNonZeroInt (rng0 : StdGen) : Int × StdGen :=
  let (v, rng1) := pickSigned257ish rng0
  (if v = 0 then 1 else v, rng1)

private def pickNonInt (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 1
  (if pick = 0 then .null else .cell Cell.empty, rng')

private def classifyQlshiftDivModr (x y shift : Int) : String :=
  if shift < 0 || shift > Int.ofNat 256 then
    "range"
  else if y = 0 then
    "divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQlshiftDivModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 29
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/boundary-valid"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftBoundary r3
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-boundary-shift"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftDivModr x y shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/signed-uniform-shift"
        #[intV x, intV y, intV shiftI], r4)
    else if shape = 3 then
      let (x, r2) := pickInt257Boundary rng1
      let (shift, r3) := pickShiftUniform r2
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftDivModr x 0 shiftI
      (mkCase s!"fuzz/shape-{shape}/{kind}/divzero"
        #[intV x, intV 0, intV shiftI], r3)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyQlshiftDivModr x y 0
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-shift0"
        #[intV x, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyQlshiftDivModr x (y * 2) 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/tie-shift1"
        #[intV x, intV (y * 2), intV 1], r3)
    else if shape = 6 then
      let kind := classifyQlshiftDivModr maxInt257 1 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/overflow-max-shift1-div1"
        #[intV maxInt257, intV 1, intV 1], rng1)
    else if shape = 7 then
      let kind := classifyQlshiftDivModr minInt257 (-1) 1
      (mkCase s!"fuzz/shape-{shape}/{kind}/overflow-min-shift1-div-neg1"
        #[intV minInt257, intV (-1), intV 1], rng1)
    else if shape = 8 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      (mkCase s!"fuzz/shape-{shape}/exact-or-inexact/zero-x"
        #[intV 0, intV y, intV (Int.ofNat shift)], r3)
    else if shape = 9 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let kind := classifyQlshiftDivModr x 1 (Int.ofNat shift)
      (mkCase s!"fuzz/shape-{shape}/{kind}/div-by-one"
        #[intV x, intV 1, intV (Int.ofNat shift)], r3)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let kind := classifyQlshiftDivModr x (-1) (Int.ofNat shift)
      (mkCase s!"fuzz/shape-{shape}/{kind}/div-by-neg-one"
        #[intV x, intV (-1), intV (Int.ofNat shift)], r3)
    else if shape = 11 then
      (mkCase s!"fuzz/shape-{shape}/range/shift-neg-one"
        #[intV 7, intV 5, intV (-1)], rng1)
    else if shape = 12 then
      (mkCase s!"fuzz/shape-{shape}/range/shift-257"
        #[intV 7, intV 5, intV 257], rng1)
    else if shape = 13 then
      (mkCase s!"fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 14 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"fuzz/shape-{shape}/underflow/one-arg"
        #[intV x], r2)
    else if shape = 15 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"fuzz/shape-{shape}/underflow/two-args"
        #[intV x, intV y], r3)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV y, nonInt], r4)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, nonInt, intV (Int.ofNat shift)], r4)
    else if shape = 18 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      let (nonInt, r4) := pickNonInt r3
      (mkCase s!"fuzz/shape-{shape}/type/pop-x-third"
        #[nonInt, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/bad-shift-y-type-first"
        #[intV x, nonInt, intV (-1)], r3)
    else if shape = 20 then
      let (y, r2) := pickNonZeroInt rng1
      let (nonInt, r3) := pickNonInt r2
      (mkCase s!"fuzz/shape-{shape}/error-order/bad-shift-x-type-third"
        #[nonInt, intV y, intV 257], r3)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-shift"
        #[.num x, .num y, .nan], r3)
    else if shape = 22 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-y"
        #[.num x, .nan, .num (Int.ofNat shift)], r3)
    else if shape = 23 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-x"
        #[.nan, .num y, .num (Int.ofNat shift)], r3)
    else if shape = 24 then
      let (shift, r2) := pickShiftUniform rng1
      (mkInputCase s!"fuzz/shape-{shape}/nan/program-both-x-y"
        #[.nan, .nan, .num (Int.ofNat shift)], r2)
    else if shape = 25 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (huge, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[.num x, .num y, .num huge], r4)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      let (huge, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[.num x, .num huge, .num (Int.ofNat shift)], r4)
    else if shape = 27 then
      let (y, r2) := pickNonZeroInt rng1
      let (shift, r3) := pickShiftUniform r2
      let (huge, r4) := pickInt257OutOfRange r3
      (mkInputCase s!"fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[.num huge, .num y, .num (Int.ofNat shift)], r4)
    else if shape = 28 then
      (mkCase s!"fuzz/shape-{shape}/error-order/range-before-y-type-via-program"
        #[intV 7, .null] #[.pushInt (.num (-1)), qlshiftDivModrInstr], rng1)
    else
      (mkCase s!"fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), qlshiftDivModrInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftDivModrId
  unit := #[
    { name := "unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 1, 5, -1),
            (-7, 3, 1, -5, 1),
            (7, -3, 1, -5, -1),
            (-7, -3, 1, 5, 1),
            (5, 2, 0, 3, -1),
            (-5, 2, 0, -2, -1),
            (5, -2, 0, -2, 1),
            (-5, -2, 0, 3, 1),
            (1, 2, 0, 1, -1),
            (-1, 2, 0, 0, -1),
            (1, -2, 0, 0, 1),
            (-1, -2, 0, 1, 1),
            (7, 5, 2, 6, -2),
            (-7, 5, 2, -6, 2),
            (7, -5, 2, -6, -2),
            (-7, -5, 2, 6, 2),
            (42, 7, 3, 48, 0),
            (0, 5, 8, 0, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectQlshiftDivModr s!"({x}<<{shift})/{y}" x y shift q r }
    ,
    { name := "unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 1, 0, maxInt257, 0),
            (maxInt257, -1, 0, -maxInt257, 0),
            (minInt257, 1, 0, minInt257, 0),
            (minInt257 + 1, -1, 0, maxInt257, 0),
            (maxInt257, 2, 0, pow2 255, -1),
            (minInt257, 2, 0, -(pow2 255), 0),
            (minInt257, -2, 0, pow2 255, 0),
            (maxInt257, 2, 1, maxInt257, 0),
            (minInt257, 2, 1, minInt257, 0),
            (1, maxInt257, 256, 1, 1),
            (-1, maxInt257, 256, -1, -1),
            (1, minInt257, 256, -1, 0),
            (-1, minInt257, 256, 1, 0)
          ]
        for c in checks do
          match c with
          | (x, y, shift, q, r) =>
              expectQlshiftDivModr s!"boundary/({x}<<{shift})/{y}" x y shift q r }
    ,
    { name := "unit/quiet/nan-and-overflow-funnels"
      run := do
        expectOkStack "quiet/divzero/nonzero-over-zero"
          (runQlshiftDivModrDirect #[intV 5, intV 0, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "quiet/divzero/zero-over-zero"
          (runQlshiftDivModrDirect #[intV 0, intV 0, intV 8]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-neg-one"
          (runQlshiftDivModrDirect #[intV 5, intV 7, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-257"
          (runQlshiftDivModrDirect #[intV 5, intV 7, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "quiet/range/shift-nan"
          (runQlshiftDivModrDirect #[intV 5, intV 7, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/y"
          (runQlshiftDivModrDirect #[intV 5, .int .nan, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "quiet/nan/x"
          (runQlshiftDivModrDirect #[.int .nan, intV 7, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "quiet/overflow/q-max-shift1-div1"
          (runQlshiftDivModrDirect #[intV maxInt257, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/q-min-shift1-div-neg1"
          (runQlshiftDivModrDirect #[intV minInt257, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/q-overmax-x-shift0-div1"
          (runQlshiftDivModrDirect #[intV (pow2 257), intV 1, intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/q-overmax-x-shift0-div2"
          (runQlshiftDivModrDirect #[intV (pow2 257), intV 2, intV 0]) #[.int .nan, intV 0]
        expectOkStack "quiet/overflow/q-undermin-x-shift0-div1"
          (runQlshiftDivModrDirect #[intV (-(pow2 257)), intV 1, intV 0]) #[.int .nan, intV 0] }
    ,
    { name := "unit/error-order/underflow-and-pop-ordering"
      run := do
        expectErr "underflow/empty" (runQlshiftDivModrDirect #[]) .stkUnd
        expectErr "underflow/one-arg" (runQlshiftDivModrDirect #[intV 1]) .stkUnd
        expectErr "underflow/two-args" (runQlshiftDivModrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "error-order/single-non-int-underflow-before-type"
          (runQlshiftDivModrDirect #[.null]) .stkUnd
        expectErr "type/pop-shift-first-null"
          (runQlshiftDivModrDirect #[intV 1, intV 2, .null]) .typeChk
        expectErr "type/pop-shift-first-cell"
          (runQlshiftDivModrDirect #[intV 1, intV 2, .cell Cell.empty]) .typeChk
        expectErr "type/pop-y-second-null"
          (runQlshiftDivModrDirect #[intV 1, .null, intV 2]) .typeChk
        expectErr "type/pop-y-second-cell"
          (runQlshiftDivModrDirect #[intV 1, .cell Cell.empty, intV 2]) .typeChk
        expectErr "type/pop-x-third-null"
          (runQlshiftDivModrDirect #[.null, intV 1, intV 2]) .typeChk
        expectErr "type/pop-x-third-cell"
          (runQlshiftDivModrDirect #[.cell Cell.empty, intV 1, intV 2]) .typeChk
        expectErr "error-order/bad-shift-y-type-first-negative"
          (runQlshiftDivModrDirect #[intV 1, .null, intV (-1)]) .typeChk
        expectErr "error-order/bad-shift-x-type-third-over256"
          (runQlshiftDivModrDirect #[.null, intV 1, intV 257]) .typeChk
        expectErr "error-order/bad-shift-y-type-first-nan"
          (runQlshiftDivModrDirect #[intV 1, .null, .int .nan]) .typeChk }
    ,
    { name := "unit/opcode/decode-qlshiftdivmodr-sequence"
      run := do
        let program : Array Instr := #[qlshiftDivModrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/qlshiftdivmodr" s0 qlshiftDivModrInstr 24
        let s2 ← expectDecodeStep "decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runQlshiftDivModrDispatchFallback #[]) #[intV 2167] }
  ]
  oracle := #[
    mkCase "ok/round/inexact-pos-pos" #[intV 7, intV 3, intV 1],
    mkCase "ok/round/inexact-neg-pos" #[intV (-7), intV 3, intV 1],
    mkCase "ok/round/inexact-pos-neg" #[intV 7, intV (-3), intV 1],
    mkCase "ok/round/inexact-neg-neg" #[intV (-7), intV (-3), intV 1],
    mkCase "ok/tie/pos-over-pos-two-shift0" #[intV 5, intV 2, intV 0],
    mkCase "ok/tie/neg-over-pos-two-shift0" #[intV (-5), intV 2, intV 0],
    mkCase "ok/tie/pos-over-neg-two-shift0" #[intV 5, intV (-2), intV 0],
    mkCase "ok/tie/neg-over-neg-two-shift0" #[intV (-5), intV (-2), intV 0],
    mkCase "ok/tie/pos-over-pos-four-shift1" #[intV 1, intV 4, intV 1],
    mkCase "ok/tie/neg-over-pos-four-shift1" #[intV (-1), intV 4, intV 1],
    mkCase "ok/tie/pos-over-neg-four-shift1" #[intV 1, intV (-4), intV 1],
    mkCase "ok/tie/neg-over-neg-four-shift1" #[intV (-1), intV (-4), intV 1],
    mkCase "ok/exact/pos-pos" #[intV 42, intV 7, intV 3],
    mkCase "ok/exact/neg-pos" #[intV (-42), intV 7, intV 3],
    mkCase "ok/exact/pos-neg" #[intV 42, intV (-7), intV 3],
    mkCase "ok/exact/neg-neg" #[intV (-42), intV (-7), intV 3],
    mkCase "ok/exact/zero-numerator" #[intV 0, intV 5, intV 8],
    mkCase "ok/boundary/max-shift0-div1" #[intV maxInt257, intV 1, intV 0],
    mkCase "ok/boundary/max-shift0-div-neg1" #[intV maxInt257, intV (-1), intV 0],
    mkCase "ok/boundary/min-shift0-div1" #[intV minInt257, intV 1, intV 0],
    mkCase "ok/boundary/min-plus-one-shift0-div-neg1" #[intV (minInt257 + 1), intV (-1), intV 0],
    mkCase "ok/boundary/max-shift0-div2" #[intV maxInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-div2" #[intV minInt257, intV 2, intV 0],
    mkCase "ok/boundary/min-shift0-div-neg2" #[intV minInt257, intV (-2), intV 0],
    mkCase "ok/boundary/max-shift1-div2" #[intV maxInt257, intV 2, intV 1],
    mkCase "ok/boundary/min-shift1-div2" #[intV minInt257, intV 2, intV 1],
    mkCase "ok/boundary/one-shift256-div-max" #[intV 1, intV maxInt257, intV 256],
    mkCase "ok/boundary/neg-one-shift256-div-max" #[intV (-1), intV maxInt257, intV 256],
    mkCase "ok/boundary/one-shift256-div-min" #[intV 1, intV minInt257, intV 256],
    mkCase "ok/boundary/neg-one-shift256-div-min" #[intV (-1), intV minInt257, intV 256],
    mkCase "quiet/divzero/nonzero-over-zero" #[intV 5, intV 0, intV 3],
    mkCase "quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 8],
    mkCase "quiet/range/shift-negative" #[intV 5, intV 7, intV (-1)],
    mkCase "quiet/range/shift-257" #[intV 5, intV 7, intV 257],
    mkCase "underflow/empty-stack" #[],
    mkCase "underflow/one-arg" #[intV 1],
    mkCase "underflow/two-args" #[intV 1, intV 2],
    mkCase "type/pop-shift-first" #[intV 1, intV 2, .null],
    mkCase "type/pop-y-second" #[intV 1, .null, intV 2],
    mkCase "type/pop-x-third" #[.null, intV 1, intV 2],
    mkCase "error-order/pop-shift-before-y-when-both-non-int" #[intV 1, .null, .cell Cell.empty],
    mkCase "error-order/bad-shift-y-type-first-negative" #[intV 1, .null, intV (-1)],
    mkCase "error-order/bad-shift-x-type-third-over256" #[.null, intV 1, intV 257],
    mkCase "error-order/range-before-y-type-via-program" #[intV 7, .null]
      #[.pushInt (.num (-1)), qlshiftDivModrInstr],
    mkCase "error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), qlshiftDivModrInstr],
    mkInputCase "nan/program-shift" #[.num 5, .num 7, .nan],
    mkInputCase "nan/program-y" #[.num 5, .nan, .num 3],
    mkInputCase "nan/program-x" #[.nan, .num 5, .num 3],
    mkInputCase "nan/program-both-x-y" #[.nan, .nan, .num 1],
    mkInputCase "error-order/pushint-overflow-shift-before-op"
      #[.num 5, .num 7, .num (maxInt257 + 1)],
    mkInputCase "error-order/pushint-underflow-shift-before-op"
      #[.num 5, .num 7, .num (minInt257 - 1)],
    mkInputCase "error-order/pushint-overflow-y-before-op"
      #[.num 5, .num (maxInt257 + 1), .num 3],
    mkInputCase "error-order/pushint-underflow-y-before-op"
      #[.num 5, .num (minInt257 - 1), .num 3],
    mkInputCase "error-order/pushint-overflow-x-before-op"
      #[.num (maxInt257 + 1), .num 5, .num 3],
    mkInputCase "error-order/pushint-underflow-x-before-op"
      #[.num (minInt257 - 1), .num 5, .num 3],
    mkInputCase "error-order/pushint-overflow-both-before-op"
      #[.num (pow2 257), .num (-(pow2 257)), .num 3],
    mkCase "gas/exact-cost-succeeds" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num qlshiftDivModrSetGasExact), .tonEnvOp .setGasLimit, qlshiftDivModrInstr],
    mkCase "gas/exact-minus-one-out-of-gas" #[intV 7, intV 5, intV 2]
      #[.pushInt (.num qlshiftDivModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftDivModrInstr]
  ]
  fuzz := #[
    { seed := 2026020832
      count := 700
      gen := genQlshiftDivModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIVMODR
