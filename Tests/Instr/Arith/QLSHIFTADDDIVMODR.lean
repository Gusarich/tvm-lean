import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Arith.QLSHIFTADDDIVMODR

/-
QLSHIFTADDDIVMODR branch-mapping notes (Lean + C++ analyzed sources):

- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Arith/Ext.lean`
    (`execInstrArithExt`, `.shlDivMod 3 0 true true none`)
  - `TvmLean/Semantics/VM/Ops/Stack.lean`
    (`popInt`, `pushIntQuiet`, underflow/type behavior)
  - `TvmLean/Model/Basics/Bytes.lean`
    (`divModRound`, nearest ties toward `+∞`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (Q-shldivmod decode family `0xb7a9c0..0xb7a9c2`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/arithops.cpp`
    (`exec_shldivmod`, add-mode remap for `d=0`, quiet registration)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`check_underflow`, `pop_long`, `pop_int`, `push_int_quiet`)
  - `/Users/daniil/Coding/ton/crypto/common/bigint.hpp`
    (`mod_div` rounding and quotient/remainder production)

Branch counts used for this suite (`d=3`, `roundMode=0`, `add=true`,
`quiet=true`, runtime shift):
- Lean specialization: ~10 branch sites / ~19 terminal outcomes
  (dispatch/fallback; pre-underflow gate; shift parse/range gate; pop order
   `shift→y→w→x`; bad-shift NaN funnel; numeric-vs-invalid split; `y=0` NaN
   branch; fixed round-mode validity branch; `d=3` dual-push quiet overflow).
- C++ specialization: ~9 branch sites / ~17 aligned terminal outcomes
  (`check_underflow`; runtime shift parse/range gate; operand-validity split;
   divisor-zero path; `mod_div` path; dual `push_int_quiet` ordering `q,r`).

Key risk areas covered:
- nearest rounding ties toward `+∞` for `(x << z) + w` over `y`;
- output order (`q` then `r`) and stack pop order (`shift`, `y`, `w`, `x`);
- quiet range behavior for runtime shifts (`z < 0`, `z > 256`, `z = NaN`);
- quiet funnels for divisor-zero, NaN operands, and quotient overflow;
- error precedence: underflow before type, and bad shift not masking `y/w/x`
  type failures in add-mode paths;
- oracle-safe NaN/out-of-range injection via program prelude (`PUSHINT`) only;
- exact gas cliff (`SETGASLIMIT` exact vs exact-minus-one).
-/

private def qlshiftAddDivModrId : InstrId := { name := "QLSHIFTADDDIVMODR" }

private def qlshiftAddDivModrInstr : Instr :=
  .arithExt (.shlDivMod 3 0 true true none)

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[qlshiftAddDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := qlshiftAddDivModrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkInputCase
    (name : String)
    (vals : Array IntVal)
    (tail : Array Instr := #[qlshiftAddDivModrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  let (stack, progPrefix) := oracleIntInputsToStackOrProgram vals
  mkCase name stack (progPrefix ++ tail) gasLimits fuel

private def runQlshiftAddDivModrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrArithExt qlshiftAddDivModrInstr stack

private def runQlshiftAddDivModrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrArithExt .add (VM.push (intV 4401)) stack

private def expectQlshiftAddDivModr
    (label : String)
    (x w y shift q r : Int) : IO Unit :=
  expectOkStack label
    (runQlshiftAddDivModrDirect #[intV x, intV w, intV y, intV shift])
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

private def qlshiftAddDivModrSetGasExact : Int :=
  computeExactGasBudget qlshiftAddDivModrInstr

private def qlshiftAddDivModrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne qlshiftAddDivModrInstr

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

private def classifyQlshiftAddDivModr (x w y shift : Int) : String :=
  if shift < 0 || shift > Int.ofNat 256 then
    "range"
  else if y = 0 then
    "divzero"
  else
    let tmp : Int := x * intPow2 shift.toNat + w
    let (q, r) := divModRound tmp y 0
    if !intFitsSigned257 q || !intFitsSigned257 r then
      "overflow"
    else if r = 0 then
      "exact"
    else if (Int.natAbs r) * 2 = Int.natAbs y then
      "tie"
    else
      "inexact"

private def genQlshiftAddDivModrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 36
  let (case0, rng2) :=
    if shape = 0 then
      let (x, r2) := pickInt257Boundary rng1
      let (w, r3) := pickInt257Boundary r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/boundary-valid"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 1 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftBoundary r4
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-boundary-shift"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 2 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (shift, r5) := pickShiftUniform r4
      let shiftI := Int.ofNat shift
      let kind := classifyQlshiftAddDivModr x w y shiftI
      (mkCase s!"/fuzz/shape-{shape}/{kind}/signed-uniform-shift"
        #[intV x, intV w, intV y, intV shiftI], r5)
    else if shape = 3 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyQlshiftAddDivModr x w 0 (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/divzero"
        #[intV x, intV w, intV 0, intV (Int.ofNat shift)], r4)
    else if shape = 4 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyQlshiftAddDivModr x 0 y 0
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-shift0-add0"
        #[intV x, intV 0, intV y, intV 0], r3)
    else if shape = 5 then
      let (x, r2) := pickFromPool tieNumeratorPool rng1
      let (y, r3) := pickFromPool tieDivisorPool r2
      let kind := classifyQlshiftAddDivModr x 1 y 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/tie-shift1-add1"
        #[intV x, intV 1, intV y, intV 1], r3)
    else if shape = 6 then
      let kind := classifyQlshiftAddDivModr maxInt257 0 1 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-max-shift1-div1"
        #[intV maxInt257, intV 0, intV 1, intV 1], rng1)
    else if shape = 7 then
      let kind := classifyQlshiftAddDivModr minInt257 0 (-1) 1
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-min-shift1-div-neg1"
        #[intV minInt257, intV 0, intV (-1), intV 1], rng1)
    else if shape = 8 then
      let kind := classifyQlshiftAddDivModr maxInt257 1 1 0
      (mkCase s!"/fuzz/shape-{shape}/{kind}/overflow-addend-overmax"
        #[intV maxInt257, intV 1, intV 1, intV 0], rng1)
    else if shape = 9 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyQlshiftAddDivModr 0 w y (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-x"
        #[intV 0, intV w, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 10 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyQlshiftAddDivModr x 0 y (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/zero-w"
        #[intV x, intV 0, intV y, intV (Int.ofNat shift)], r4)
    else if shape = 11 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyQlshiftAddDivModr x w 1 (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-one"
        #[intV x, intV w, intV 1, intV (Int.ofNat shift)], r4)
    else if shape = 12 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let kind := classifyQlshiftAddDivModr x w (-1) (Int.ofNat shift)
      (mkCase s!"/fuzz/shape-{shape}/{kind}/div-by-neg-one"
        #[intV x, intV w, intV (-1), intV (Int.ofNat shift)], r4)
    else if shape = 13 then
      (mkCase s!"/fuzz/shape-{shape}/range/shift-neg-one"
        #[intV 7, intV 3, intV 5, intV (-1)], rng1)
    else if shape = 14 then
      (mkCase s!"/fuzz/shape-{shape}/range/shift-257"
        #[intV 7, intV 3, intV 5, intV 257], rng1)
    else if shape = 15 then
      (mkCase s!"/fuzz/shape-{shape}/underflow/empty" #[], rng1)
    else if shape = 16 then
      let (x, r2) := pickSigned257ish rng1
      (mkCase s!"/fuzz/shape-{shape}/underflow/one-arg"
        #[intV x], r2)
    else if shape = 17 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/underflow/two-args"
        #[intV x, intV w], r3)
    else if shape = 18 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkCase s!"/fuzz/shape-{shape}/underflow/three-args"
        #[intV x, intV w, intV y], r4)
    else if shape = 19 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-shift-first"
        #[intV x, intV w, intV y, nonInt], r5)
    else if shape = 20 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-y-second"
        #[intV x, intV w, nonInt, intV (Int.ofNat shift)], r5)
    else if shape = 21 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-w-third"
        #[intV x, nonInt, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 22 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (nonInt, r5) := pickNonInt r4
      (mkCase s!"/fuzz/shape-{shape}/type/pop-x-fourth"
        #[nonInt, intV w, intV y, intV (Int.ofNat shift)], r5)
    else if shape = 23 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-y-type-first-negative"
        #[intV x, intV w, .null, intV (-1)], r3)
    else if shape = 24 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-w-type-third-over256"
        #[intV x, .null, intV y, intV 257], r3)
    else if shape = 25 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      (mkCase s!"/fuzz/shape-{shape}/error-order/bad-shift-x-type-fourth-negative"
        #[.null, intV w, intV y, intV (-1)], r3)
    else if shape = 26 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-shift"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.nan], r4)
    else if shape = 27 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-y"
        #[IntVal.num x, IntVal.num w, IntVal.nan, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 28 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-w"
        #[IntVal.num x, IntVal.nan, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 29 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-x"
        #[IntVal.nan, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r4)
    else if shape = 30 then
      let (w, r2) := pickSigned257ish rng1
      let (shift, r3) := pickShiftUniform r2
      (mkInputCase s!"/fuzz/shape-{shape}/nan/program-both-x-y"
        #[IntVal.nan, IntVal.num w, IntVal.nan, IntVal.num (Int.ofNat shift)], r3)
    else if shape = 31 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (y, r4) := pickNonZeroInt r3
      let (pickNeg, r5) := randBool r4
      let huge : Int := if pickNeg then -1 else 257
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-shift-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num y, IntVal.num huge], r5)
    else if shape = 32 then
      let (x, r2) := pickSigned257ish rng1
      let (w, r3) := pickSigned257ish r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-y-before-op"
        #[IntVal.num x, IntVal.num w, IntVal.num huge, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 33 then
      let (x, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-w-before-op"
        #[IntVal.num x, IntVal.num huge, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 34 then
      let (w, r2) := pickSigned257ish rng1
      let (y, r3) := pickNonZeroInt r2
      let (shift, r4) := pickShiftUniform r3
      let (huge, r5) := pickInt257OutOfRange r4
      (mkInputCase s!"/fuzz/shape-{shape}/error-order/pushint-overflow-x-before-op"
        #[IntVal.num huge, IntVal.num w, IntVal.num y, IntVal.num (Int.ofNat shift)], r5)
    else if shape = 35 then
      (mkCase s!"/fuzz/shape-{shape}/error-order/range-before-y-type-via-program"
        #[intV 7, intV 3, .null] #[.pushInt (.num (-1)), qlshiftAddDivModrInstr], rng1)
    else
      (mkCase s!"/fuzz/shape-{shape}/error-order/underflow-before-range-via-program"
        #[] #[.pushInt (.num (-1)), qlshiftAddDivModrInstr], rng1)
  let (tag, rng3) := randNat rng2 0 999_999
  ({ case0 with name := s!"{case0.name}/{tag}" }, rng3)

def suite : InstrSuite where
  id := qlshiftAddDivModrId
  unit := #[
    { name := "/unit/ok/nearest-rounding-and-output-order"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (7, 3, 5, 1, 3, 2),
            (-7, 3, 5, 1, -2, -1),
            (7, -3, 5, 1, 2, 1),
            (-7, -3, 5, 1, -3, -2),
            (7, 3, -5, 1, -3, 2),
            (-7, 3, -5, 1, 2, -1),
            (5, 0, 2, 0, 3, -1),
            (-5, 0, 2, 0, -2, -1),
            (5, 0, -2, 0, -2, 1),
            (-5, 0, -2, 0, 3, 1),
            (1, 0, 2, 0, 1, -1),
            (-1, 0, 2, 0, 0, -1),
            (1, 0, -2, 0, 0, 1),
            (-1, 0, -2, 0, 1, 1),
            (7, 5, 2, 2, 17, -1),
            (-7, 5, 2, 2, -11, -1),
            (7, -5, 2, 2, 12, -1),
            (-7, -5, 2, 2, -16, -1),
            (42, 0, 7, 3, 48, 0),
            (0, 9, 5, 8, 2, -1),
            (0, -9, 5, 8, -2, 1),
            (3, 1, 5, 0, 1, -1)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectQlshiftAddDivModr s!"/check/({x}<<{shift})+{w}/{y}" x w y shift q r }
    ,
    { name := "/unit/ok/boundary-successes"
      run := do
        let checks : Array (Int × Int × Int × Int × Int × Int) :=
          #[
            (maxInt257, 0, 1, 0, maxInt257, 0),
            (maxInt257, -1, 1, 0, maxInt257 - 1, 0),
            (minInt257, 1, 1, 0, minInt257 + 1, 0),
            (minInt257 + 1, 0, -1, 0, maxInt257, 0),
            (maxInt257, 0, 2, 0, pow2 255, -1),
            (minInt257, 0, 2, 0, -(pow2 255), 0),
            (minInt257, 0, -2, 0, pow2 255, 0),
            (1, 0, maxInt257, 256, 1, 1),
            (-1, 0, maxInt257, 256, -1, -1),
            (1, 0, minInt257, 256, -1, 0),
            (-1, 0, minInt257, 256, 1, 0),
            (0, maxInt257, maxInt257, 0, 1, 0),
            (0, minInt257, minInt257, 0, 1, 0),
            (1, -1, maxInt257, 256, 1, 0)
          ]
        for c in checks do
          match c with
          | (x, w, y, shift, q, r) =>
              expectQlshiftAddDivModr s!"/boundary/({x}<<{shift})+{w}/{y}" x w y shift q r }
    ,
    { name := "/unit/quiet/nan-divzero-range-overflow-and-pop-funnels"
      run := do
        expectOkStack "/quiet/divzero/nonzero-over-zero"
          (runQlshiftAddDivModrDirect #[intV 5, intV 1, intV 0, intV 3]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/divzero/zero-over-zero"
          (runQlshiftAddDivModrDirect #[intV 0, intV 0, intV 0, intV 8]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/range/shift-neg-one"
          (runQlshiftAddDivModrDirect #[intV 5, intV 3, intV 7, intV (-1)]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/range/shift-257"
          (runQlshiftAddDivModrDirect #[intV 5, intV 3, intV 7, intV 257]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/range/shift-nan"
          (runQlshiftAddDivModrDirect #[intV 5, intV 3, intV 7, .int .nan]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/y"
          (runQlshiftAddDivModrDirect #[intV 5, intV 3, .int .nan, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/w"
          (runQlshiftAddDivModrDirect #[intV 5, .int .nan, intV 7, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/nan/x"
          (runQlshiftAddDivModrDirect #[.int .nan, intV 3, intV 7, intV 1]) #[.int .nan, .int .nan]
        expectOkStack "/quiet/overflow/q-max-shift1-div1"
          (runQlshiftAddDivModrDirect #[intV maxInt257, intV 0, intV 1, intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/q-min-shift1-div-neg1"
          (runQlshiftAddDivModrDirect #[intV minInt257, intV 0, intV (-1), intV 1]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/q-addend-overmax"
          (runQlshiftAddDivModrDirect #[intV maxInt257, intV 1, intV 1, intV 0]) #[.int .nan, intV 0]
        expectOkStack "/quiet/overflow/q-addend-undermin"
          (runQlshiftAddDivModrDirect #[intV minInt257, intV (-1), intV 1, intV 0]) #[.int .nan, intV 0]
        expectOkStack "/quiet/pop-order/lower-preserved"
          (runQlshiftAddDivModrDirect #[.cell Cell.empty, intV 7, intV 3, intV 5, intV 1])
          #[.cell Cell.empty, intV 3, intV 2]
        expectOkStack "/quiet/pop-order/lower-preserved-range-shift"
          (runQlshiftAddDivModrDirect #[.cell Cell.empty, intV 7, intV 3, intV 5, intV 257])
          #[.cell Cell.empty, .int .nan, .int .nan] }
    ,
    { name := "/unit/error-order/underflow-and-pop-type-ordering"
      run := do
        expectErr "/underflow/empty" (runQlshiftAddDivModrDirect #[]) .stkUnd
        expectErr "/underflow/one-arg" (runQlshiftAddDivModrDirect #[intV 1]) .stkUnd
        expectErr "/underflow/two-args" (runQlshiftAddDivModrDirect #[intV 1, intV 2]) .stkUnd
        expectErr "/underflow/three-args" (runQlshiftAddDivModrDirect #[intV 1, intV 2, intV 3]) .stkUnd
        expectErr "/error-order/underflow-before-type-with-three-items"
          (runQlshiftAddDivModrDirect #[.null, .cell Cell.empty, intV 1]) .stkUnd
        expectErr "/type/pop-shift-first-null"
          (runQlshiftAddDivModrDirect #[intV 1, intV 2, intV 3, .null]) .typeChk
        expectErr "/type/pop-shift-first-cell"
          (runQlshiftAddDivModrDirect #[intV 1, intV 2, intV 3, .cell Cell.empty]) .typeChk
        expectErr "/type/pop-y-second-null"
          (runQlshiftAddDivModrDirect #[intV 1, intV 2, .null, intV 3]) .typeChk
        expectErr "/type/pop-w-third-null"
          (runQlshiftAddDivModrDirect #[intV 1, .null, intV 2, intV 3]) .typeChk
        expectErr "/type/pop-x-fourth-null"
          (runQlshiftAddDivModrDirect #[.null, intV 1, intV 2, intV 3]) .typeChk
        expectErr "/error-order/pop-shift-before-y-when-both-non-int"
          (runQlshiftAddDivModrDirect #[intV 1, intV 2, .null, .cell Cell.empty]) .typeChk
        expectErr "/error-order/bad-shift-y-type-first-negative"
          (runQlshiftAddDivModrDirect #[intV 1, intV 2, .null, intV (-1)]) .typeChk
        expectErr "/error-order/bad-shift-w-type-third-over256"
          (runQlshiftAddDivModrDirect #[intV 1, .null, intV 2, intV 257]) .typeChk
        expectErr "/error-order/bad-shift-x-type-fourth-nan"
          (runQlshiftAddDivModrDirect #[.null, intV 1, intV 2, .int .nan]) .typeChk }
    ,
    { name := "/unit/opcode/decode-qlshiftadddivmodr-sequence"
      run := do
        let program : Array Instr := #[qlshiftAddDivModrInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "/decode/qlshiftadddivmodr" s0 qlshiftAddDivModrInstr 24
        let s2 ← expectDecodeStep "/decode/tail-add" s1 .add 8
        if s2.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"/decode/end: expected exhausted slice, got {s2.bitsRemaining} bits remaining") }
    ,
    { name := "/unit/dispatch/non-arithext-falls-through"
      run := do
        expectOkStack "/dispatch/fallback"
          (runQlshiftAddDivModrDispatchFallback #[]) #[intV 4401] }
  ]
  oracle := #[
    mkCase "/ok/round/inexact-pos-pos" #[intV 7, intV 3, intV 5, intV 1],
    mkCase "/ok/round/inexact-neg-pos" #[intV (-7), intV 3, intV 5, intV 1],
    mkCase "/ok/round/inexact-pos-neg" #[intV 7, intV 3, intV (-5), intV 1],
    mkCase "/ok/round/inexact-neg-neg" #[intV (-7), intV 3, intV (-5), intV 1],
    mkCase "/ok/tie/pos-over-pos-two-shift0" #[intV 5, intV 0, intV 2, intV 0],
    mkCase "/ok/tie/neg-over-pos-two-shift0" #[intV (-5), intV 0, intV 2, intV 0],
    mkCase "/ok/tie/pos-over-neg-two-shift0" #[intV 5, intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/neg-over-neg-two-shift0" #[intV (-5), intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/near-zero-pos-over-pos-two" #[intV 1, intV 0, intV 2, intV 0],
    mkCase "/ok/tie/near-zero-neg-over-pos-two" #[intV (-1), intV 0, intV 2, intV 0],
    mkCase "/ok/tie/near-zero-pos-over-neg-two" #[intV 1, intV 0, intV (-2), intV 0],
    mkCase "/ok/tie/near-zero-neg-over-neg-two" #[intV (-1), intV 0, intV (-2), intV 0],
    mkCase "/ok/exact/shifted-divisible" #[intV 42, intV 0, intV 7, intV 3],
    mkCase "/ok/exact/addend-only-positive" #[intV 0, intV 9, intV 5, intV 8],
    mkCase "/ok/exact/addend-only-negative" #[intV 0, intV (-9), intV 5, intV 8],
    mkCase "/ok/exact/addend-cancels-to-divisible" #[intV 1, intV (-1), intV maxInt257, intV 256],
    mkCase "/ok/boundary/max-shift0-div1" #[intV maxInt257, intV 0, intV 1, intV 0],
    mkCase "/ok/boundary/max-plus-negone-shift0-div1" #[intV maxInt257, intV (-1), intV 1, intV 0],
    mkCase "/ok/boundary/min-plus-one-shift0-div1" #[intV minInt257, intV 1, intV 1, intV 0],
    mkCase "/ok/boundary/min-plus-one-shift0-div-neg1" #[intV (minInt257 + 1), intV 0, intV (-1), intV 0],
    mkCase "/ok/boundary/max-shift0-div2" #[intV maxInt257, intV 0, intV 2, intV 0],
    mkCase "/ok/boundary/min-shift0-div2" #[intV minInt257, intV 0, intV 2, intV 0],
    mkCase "/ok/boundary/min-shift0-div-neg2" #[intV minInt257, intV 0, intV (-2), intV 0],
    mkCase "/ok/boundary/one-shift256-div-max" #[intV 1, intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/neg-one-shift256-div-max" #[intV (-1), intV 0, intV maxInt257, intV 256],
    mkCase "/ok/boundary/one-shift256-div-min" #[intV 1, intV 0, intV minInt257, intV 256],
    mkCase "/ok/boundary/neg-one-shift256-div-min" #[intV (-1), intV 0, intV minInt257, intV 256],
    mkCase "/ok/boundary/w-max-over-max" #[intV 0, intV maxInt257, intV maxInt257, intV 0],
    mkCase "/ok/boundary/w-min-over-min" #[intV 0, intV minInt257, intV minInt257, intV 0],
    mkCase "/quiet/divzero/nonzero-over-zero" #[intV 5, intV 1, intV 0, intV 3],
    mkCase "/quiet/divzero/zero-over-zero" #[intV 0, intV 0, intV 0, intV 8],
    mkCase "/quiet/range/shift-negative" #[intV 5, intV 3, intV 7, intV (-1)],
    mkCase "/quiet/range/shift-257" #[intV 5, intV 3, intV 7, intV 257],
    mkCase "/quiet/overflow/max-shift1-div1" #[intV maxInt257, intV 0, intV 1, intV 1],
    mkCase "/quiet/overflow/min-shift1-div-neg1" #[intV minInt257, intV 0, intV (-1), intV 1],
    mkCase "/quiet/overflow/addend-overmax" #[intV maxInt257, intV 1, intV 1, intV 0],
    mkCase "/quiet/overflow/addend-undermin" #[intV minInt257, intV (-1), intV 1, intV 0],
    mkCase "/underflow/empty-stack" #[],
    mkCase "/underflow/one-arg" #[intV 1],
    mkCase "/underflow/two-args" #[intV 1, intV 2],
    mkCase "/underflow/three-args" #[intV 1, intV 2, intV 3],
    mkCase "/type/pop-shift-first" #[intV 1, intV 2, intV 3, .null],
    mkCase "/type/pop-y-second" #[intV 1, intV 2, .null, intV 3],
    mkCase "/type/pop-w-third" #[intV 1, .null, intV 2, intV 3],
    mkCase "/type/pop-x-fourth" #[.null, intV 1, intV 2, intV 3],
    mkCase "/error-order/underflow-before-type-with-three-items" #[.null, .cell Cell.empty, intV 1],
    mkCase "/error-order/pop-shift-before-y-when-both-non-int" #[intV 1, intV 2, .null, .cell Cell.empty],
    mkCase "/error-order/bad-shift-y-type-first-negative" #[intV 1, intV 2, .null, intV (-1)],
    mkCase "/error-order/bad-shift-w-type-third-over256" #[intV 1, .null, intV 2, intV 257],
    mkCase "/error-order/bad-shift-x-type-fourth-nan" #[.null, intV 1, intV 2]
      #[.pushInt .nan, qlshiftAddDivModrInstr],
    mkCase "/pop-order/lower-preserved" #[.cell Cell.empty, intV 7, intV 3, intV 5, intV 1],
    mkCase "/pop-order/lower-preserved-range-shift" #[.cell Cell.empty, intV 7, intV 3, intV 5, intV 257],
    mkCase "/error-order/range-before-y-type-via-program" #[intV 7, intV 3, .null]
      #[.pushInt (.num (-1)), qlshiftAddDivModrInstr],
    mkCase "/error-order/range-before-w-type-via-program" #[intV 7, .null, intV 5]
      #[.pushInt (.num 257), qlshiftAddDivModrInstr],
    mkCase "/error-order/underflow-before-range-via-program" #[]
      #[.pushInt (.num (-1)), qlshiftAddDivModrInstr],
    mkInputCase "/nan/program-shift" #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.nan],
    mkInputCase "/nan/program-y" #[IntVal.num 5, IntVal.num 3, IntVal.nan, IntVal.num 1],
    mkInputCase "/nan/program-w" #[IntVal.num 5, IntVal.nan, IntVal.num 7, IntVal.num 1],
    mkInputCase "/nan/program-x" #[IntVal.nan, IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkInputCase "/nan/program-both-x-y" #[IntVal.nan, IntVal.num 3, IntVal.nan, IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-shift-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.num (maxInt257 + 1)],
    mkInputCase "/error-order/pushint-underflow-shift-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num 7, IntVal.num (minInt257 - 1)],
    mkInputCase "/error-order/pushint-overflow-y-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (maxInt257 + 1), IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-y-before-op"
      #[IntVal.num 5, IntVal.num 3, IntVal.num (minInt257 - 1), IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-w-before-op"
      #[IntVal.num 5, IntVal.num (pow2 257), IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-w-before-op"
      #[IntVal.num 5, IntVal.num (-(pow2 257)), IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-overflow-x-before-op"
      #[IntVal.num (maxInt257 + 1), IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkInputCase "/error-order/pushint-underflow-x-before-op"
      #[IntVal.num (minInt257 - 1), IntVal.num 3, IntVal.num 7, IntVal.num 1],
    mkCase "/gas/exact-cost-succeeds" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num qlshiftAddDivModrSetGasExact), .tonEnvOp .setGasLimit, qlshiftAddDivModrInstr],
    mkCase "/gas/exact-minus-one-out-of-gas" #[intV 7, intV 3, intV 5, intV 1]
      #[.pushInt (.num qlshiftAddDivModrSetGasExactMinusOne), .tonEnvOp .setGasLimit, qlshiftAddDivModrInstr]
  ]
  fuzz := #[
    { seed := 2026020843
      count := 700
      gen := genQlshiftAddDivModrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTADDDIVMODR
